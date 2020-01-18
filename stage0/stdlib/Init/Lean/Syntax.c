// Lean compiler output
// Module: Init.Lean.Syntax
// Imports: Init.Data.Array Init.Lean.Data.Name Init.Lean.Data.Format
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
lean_object* l_Lean_Syntax_reprint___main___closed__1;
lean_object* l_Lean_Syntax_formatStxAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Syntax_reprint___main___boxed(lean_object*);
lean_object* l_Lean_Syntax_isIdOrAtom_x3f___boxed(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Syntax_4__reprintLeaf(lean_object*, lean_object*);
lean_object* l_Lean_fieldIdxKind;
lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object*);
lean_object* l___private_Init_Lean_Syntax_1__updateInfo(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfoAux(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Syntax_6__decodeOctalLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Syntax_10__decodeNatLitVal___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_reprint___boxed(lean_object*);
lean_object* l___private_Init_Lean_Syntax_10__decodeNatLitVal___boxed(lean_object*);
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_nullKind;
lean_object* l_Lean_Syntax_modifyArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fieldIdxKind___closed__2;
lean_object* l_Lean_Syntax_formatStxAux___main___closed__5;
lean_object* l_Lean_Syntax_ifNodeKind___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__14;
lean_object* l_Array_findMAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isAtom___boxed(lean_object*);
lean_object* l_Lean_Syntax_mrewriteBottomUp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_toNat___boxed(lean_object*);
lean_object* l___private_Init_Lean_Syntax_5__decodeBinLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_HasToString;
lean_object* l___private_Init_Lean_Syntax_5__decodeBinLitAux___main___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_SyntaxNode_withArgs(lean_object*);
lean_object* l___private_Init_Lean_Syntax_5__decodeBinLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fieldIdxKind___closed__1;
lean_object* l_Lean_Syntax_mreplace___main___boxed(lean_object*);
lean_object* l___private_Init_Lean_Syntax_11__decodeQuotedChar(lean_object*, lean_object*);
uint8_t l_Char_isDigit(uint32_t);
lean_object* l_Lean_charLitKind___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Syntax_4__reprintLeaf___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_reprint___main(lean_object*);
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mrewriteBottomUp(lean_object*);
lean_object* l_Lean_Syntax_ifNodeKind(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_charLitKind___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__6;
lean_object* l_Lean_Syntax_setAtomVal(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_SyntaxNode_getArg___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Syntax_8__decodeHexLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Syntax_6__decodeOctalLitAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo___main___boxed(lean_object*);
lean_object* l___private_Init_Lean_Syntax_3__updateLast___main___at_Lean_Syntax_setTailInfoAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_mkIdentFrom___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeStrLitAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mreplace___main(lean_object*);
lean_object* l_Lean_Syntax_Lean_HasFormat(lean_object*);
lean_object* l_Lean_Syntax_mreplace___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Syntax_3__updateLast___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___boxed(lean_object*);
lean_object* l_Lean_Syntax_modifyArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__1;
lean_object* l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__2;
lean_object* l_Lean_SyntaxNode_getKind(lean_object*);
lean_object* l_Lean_SyntaxNode_getArgs(lean_object*);
lean_object* l_Lean_Syntax_rewriteBottomUp(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Syntax_5__decodeBinLitAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__3;
lean_object* l_Lean_Syntax_formatStxAux___main___closed__8;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_ifNode(lean_object*);
lean_object* l___private_Init_Lean_Syntax_8__decodeHexLitAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__4;
lean_object* l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__1;
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__4;
lean_object* l_Array_findRevMAux___main___at_Lean_Syntax_getTailInfo___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStxNumLit(lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_getIdAt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Syntax_7__decodeHexDigit___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_getKind___boxed(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_updateTrailing(lean_object*, lean_object*);
lean_object* l_Lean_numLitKind;
lean_object* l_Lean_choiceKind___closed__1;
lean_object* l_Lean_Syntax_mreplace___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_choiceKind___closed__2;
lean_object* l_Lean_strLitKind;
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId___boxed(lean_object*);
lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_numLitKind___closed__1;
lean_object* l_Lean_unreachIsNodeMissing(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getIdAt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object*);
lean_object* l_Lean_Syntax_formatStx___boxed(lean_object*, lean_object*);
lean_object* l_Lean_strLitKind___closed__1;
lean_object* l_Lean_Syntax_isNatLitAux___boxed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Syntax_3__updateLast(lean_object*);
lean_object* l_Lean_Syntax_updateLeading(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__3;
lean_object* l_Lean_mkNullNode(lean_object*);
lean_object* l_Lean_Syntax_getPos___boxed(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__15;
lean_object* l_Lean_strLitKind___closed__2;
lean_object* l_Lean_Syntax_setArgs(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__9;
lean_object* l___private_Init_Lean_Syntax_7__decodeHexDigit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_choiceKind;
lean_object* l_Lean_charLitKind;
lean_object* l_Lean_SourceInfo_truncateTrailing(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Syntax_rewriteBottomUp___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_numLitKind___closed__2;
lean_object* l_Lean_Syntax_isMissing___boxed(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Syntax_8__decodeHexLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mreplace(lean_object*);
lean_object* l___private_Init_Lean_Syntax_3__updateLast___main(lean_object*);
lean_object* l___private_Init_Lean_Syntax_9__decodeDecimalLitAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_Lean_SyntaxNode_modifyArgs(lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_getArgs___boxed(lean_object*);
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_unreachIsNodeIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_Iterator_HasRepr___closed__2;
lean_object* l_Lean_SourceInfo_appendToLeading(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_getTailInfo___main___boxed(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__12;
lean_object* l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__2;
lean_object* l_Lean_nullKind___closed__1;
lean_object* l_Lean_Syntax_ifNode___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_asNode___boxed(lean_object*);
lean_object* l_Lean_Syntax_decodeStrLit___boxed(lean_object*);
lean_object* l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__11;
lean_object* l_Lean_SyntaxNode_getNumArgs___boxed(lean_object*);
lean_object* l_Lean_Syntax_decodeCharLit(lean_object*);
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_updateTrailing___main(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAtom(lean_object*);
lean_object* l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_nullKind___closed__2;
extern lean_object* l_Lean_Format_sbracket___closed__3;
lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object*);
lean_object* l___private_Init_Lean_Syntax_6__decodeOctalLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_unreachIsNodeAtom(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo___main(lean_object*);
extern lean_object* l_Lean_formatDataValue___closed__2;
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Array_umapMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object*);
extern lean_object* l_Lean_HasRepr___closed__1;
lean_object* l_Lean_Syntax_setArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_appendToTrailing(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_getNumArgs(lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
extern lean_object* l_Lean_Format_paren___closed__1;
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Syntax_mrewriteBottomUp___boxed(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__13;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_updateTrailing(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Syntax_8__decodeHexLitAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Syntax_2__updateLeadingAux(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_hasArgs(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Syntax_asNode___closed__1;
lean_object* l_Lean_Syntax_HasToString___closed__2;
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_withArgs___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__1;
lean_object* l_Lean_Syntax_getHeadInfo___boxed(lean_object*);
extern lean_object* l_Lean_Format_paren___closed__2;
lean_object* l_Lean_unreachIsNodeAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Syntax_3__updateLast___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfoAux___main(lean_object*, lean_object*);
lean_object* lean_format_group(lean_object*);
lean_object* l_Lean_mkStxStrLit(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l___private_Init_Lean_Syntax_9__decodeDecimalLitAux___main(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_atom(lean_object*);
lean_object* l___private_Init_Lean_Syntax_9__decodeDecimalLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_num_lit(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Syntax_updateLeading___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_HasToString___closed__1;
lean_object* l_Array_findRevMAux___main___at_Lean_Syntax_getTailInfo___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_Syntax_mrewriteBottomUp___main(lean_object*);
lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* l_Lean_Syntax_HasToString___lambda__1(lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___at_Lean_Syntax_rewriteBottomUp___spec__1(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeStrLit(lean_object*);
lean_object* lean_mk_syntax_list(lean_object*);
lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object*);
lean_object* l___private_Init_Lean_Syntax_10__decodeNatLitVal(lean_object*);
lean_object* l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__5;
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Syntax_mreplace___boxed(lean_object*);
lean_object* lean_mk_syntax_str_lit(lean_object*);
lean_object* l_Lean_mkStxLit(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Syntax_9__decodeDecimalLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_toNat(lean_object*);
extern lean_object* l_Lean_Format_paren___closed__3;
lean_object* l_Lean_Syntax_formatStxAux___main___closed__10;
lean_object* l_Lean_Syntax_asNode(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_unreachIsNodeIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeStrLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtomFrom___boxed(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
uint8_t l_UInt32_decLe(uint32_t, uint32_t);
lean_object* l_Lean_Syntax_ifNodeKind___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_modifyArgs(lean_object*, lean_object*);
lean_object* l_Lean_mkNode(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_Syntax_getTailInfo___main(lean_object*);
lean_object* l_Lean_Syntax_decodeStrLitAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SyntaxNode_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main___closed__7;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_reprint(lean_object*);
lean_object* l___private_Init_Lean_Syntax_6__decodeOctalLitAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isIdent___boxed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_SourceInfo_updateTrailing(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 2);
lean_dec(x_4);
lean_ctor_set(x_1, 2, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_2);
return x_7;
}
}
}
lean_object* l_Lean_SourceInfo_truncateTrailing(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
lean_dec(x_6);
lean_inc(x_5);
lean_ctor_set(x_3, 2, x_5);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_1, 2, x_9);
return x_1;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 x_15 = x_10;
} else {
 lean_dec_ref(x_10);
 x_15 = lean_box(0);
}
lean_inc(x_14);
if (lean_is_scalar(x_15)) {
 x_16 = lean_alloc_ctor(0, 3, 0);
} else {
 x_16 = x_15;
}
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_14);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
}
lean_object* l_Lean_SourceInfo_appendToTrailing(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 2);
lean_dec(x_6);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_4, 0);
lean_dec(x_11);
lean_ctor_set(x_4, 1, x_8);
lean_ctor_set(x_4, 0, x_7);
lean_ctor_set(x_1, 2, x_4);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_1, 2, x_13);
return x_1;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_ctor_get(x_4, 2);
lean_inc(x_18);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 x_19 = x_4;
} else {
 lean_dec_ref(x_4);
 x_19 = lean_box(0);
}
if (lean_is_scalar(x_19)) {
 x_20 = lean_alloc_ctor(0, 3, 0);
} else {
 x_20 = x_19;
}
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_20);
return x_21;
}
}
}
lean_object* l_Lean_SourceInfo_appendToLeading(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_dec(x_6);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_4, 0);
lean_dec(x_11);
lean_ctor_set(x_4, 2, x_8);
lean_ctor_set(x_4, 0, x_7);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 2);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 x_19 = x_4;
} else {
 lean_dec_ref(x_4);
 x_19 = lean_box(0);
}
if (lean_is_scalar(x_19)) {
 x_20 = lean_alloc_ctor(0, 3, 0);
} else {
 x_20 = x_19;
}
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_17);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_15);
return x_21;
}
}
}
lean_object* _init_l_Lean_choiceKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("choice");
return x_1;
}
}
lean_object* _init_l_Lean_choiceKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_choiceKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_choiceKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_choiceKind___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_nullKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("null");
return x_1;
}
}
lean_object* _init_l_Lean_nullKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_nullKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_nullKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_nullKind___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_strLitKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("strLit");
return x_1;
}
}
lean_object* _init_l_Lean_strLitKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_strLitKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_strLitKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_strLitKind___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_charLitKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("charLit");
return x_1;
}
}
lean_object* _init_l_Lean_charLitKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_charLitKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_charLitKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_charLitKind___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_numLitKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("numLit");
return x_1;
}
}
lean_object* _init_l_Lean_numLitKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_numLitKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_numLitKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_numLitKind___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_fieldIdxKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fieldIdx");
return x_1;
}
}
lean_object* _init_l_Lean_fieldIdxKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_fieldIdxKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_fieldIdxKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_fieldIdxKind___closed__2;
return x_1;
}
}
uint8_t l_Lean_Syntax_isMissing(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Syntax_isMissing___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isMissing(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_unreachIsNodeMissing(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_panic_unreachable();
}
}
lean_object* l_Lean_unreachIsNodeAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_panic_unreachable();
}
}
lean_object* l_Lean_unreachIsNodeAtom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_unreachIsNodeAtom(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_unreachIsNodeIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_panic_unreachable();
}
}
lean_object* l_Lean_unreachIsNodeIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_unreachIsNodeIdent(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_SyntaxNode_getKind(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_SyntaxNode_getKind___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SyntaxNode_getKind(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SyntaxNode_withArgs___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_SyntaxNode_withArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SyntaxNode_withArgs___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_SyntaxNode_getNumArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
lean_object* l_Lean_SyntaxNode_getNumArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SyntaxNode_getNumArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SyntaxNode_getArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Syntax_inhabited;
x_5 = lean_array_get(x_4, x_3, x_2);
return x_5;
}
}
lean_object* l_Lean_SyntaxNode_getArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SyntaxNode_getArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SyntaxNode_getArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_SyntaxNode_getArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SyntaxNode_getArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SyntaxNode_modifyArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_apply_1(x_2, x_4);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_apply_1(x_2, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Syntax_setAtomVal(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Lean_Syntax_ifNode___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = lean_apply_1(x_2, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_ifNode(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_ifNode___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_ifNodeKind___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_name_eq(x_5, x_2);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_4, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Syntax_ifNodeKind(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_ifNodeKind___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_ifNodeKind___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_ifNodeKind___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
uint8_t l_Lean_Syntax_isAtom(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Syntax_isAtom___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isAtom(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Syntax_isIdent(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Syntax_isIdent___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isIdent(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_getId(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
}
lean_object* l_Lean_Syntax_getId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Syntax_asNode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_asNode(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_asNode___closed__1;
return x_2;
}
}
}
lean_object* l_Lean_Syntax_asNode___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_asNode(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_getNumArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Syntax_asNode(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_getNumArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getNumArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_setArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Lean_Syntax_modifyArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_apply_1(x_2, x_4);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_apply_1(x_2, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Lean_Syntax_setArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_set(x_5, x_2, x_3);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_array_set(x_8, x_2, x_3);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
lean_dec(x_3);
return x_1;
}
}
}
lean_object* l_Lean_Syntax_setArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_setArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Syntax_modifyArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_5, x_2);
x_9 = lean_box(0);
x_10 = lean_array_fset(x_5, x_2, x_9);
x_11 = lean_apply_1(x_3, x_8);
x_12 = lean_array_fset(x_10, x_2, x_11);
lean_ctor_set(x_1, 1, x_12);
return x_1;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = lean_array_get_size(x_14);
x_16 = lean_nat_dec_lt(x_2, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_array_fget(x_14, x_2);
x_19 = lean_box(0);
x_20 = lean_array_fset(x_14, x_2, x_19);
x_21 = lean_apply_1(x_3, x_18);
x_22 = lean_array_fset(x_20, x_2, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_dec(x_3);
return x_1;
}
}
}
lean_object* l_Lean_Syntax_modifyArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_modifyArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Syntax_getIdAt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getId(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_getIdAt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_getIdAt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
}
}
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_mreplace___main___rarg(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Syntax_mreplace___main___rarg___lambda__2___boxed), 4, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_9 = l_Array_umapMAux___main___rarg(x_1, lean_box(0), x_7, x_8, x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_Syntax_mreplace___main___rarg___lambda__3), 3, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_4);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_12);
return x_15;
}
}
}
lean_object* l_Lean_Syntax_mreplace___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_2);
x_13 = lean_apply_1(x_2, x_3);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Syntax_mreplace___main___rarg___lambda__4), 6, 5);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_11);
lean_closure_set(x_14, 3, x_10);
lean_closure_set(x_14, 4, x_12);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_box(0);
x_4 = x_16;
goto block_9;
}
block_9:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_3);
x_6 = lean_apply_1(x_2, x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_Syntax_mreplace___main___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_3);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Syntax_mreplace___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_mreplace___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_mreplace___main___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_mreplace___main___rarg___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Syntax_mreplace___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_mreplace___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_mreplace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_mreplace___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_mreplace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_mreplace___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_mreplace___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_mreplace(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_mrewriteBottomUp___main___rarg(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__1___boxed), 4, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_umapMAux___main___rarg(x_1, lean_box(0), x_7, x_8, x_5);
x_10 = lean_alloc_closure((void*)(l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__2), 3, 2);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_2);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = lean_apply_1(x_2, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Syntax_mrewriteBottomUp___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_mrewriteBottomUp___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_mrewriteBottomUp___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_mrewriteBottomUp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_mrewriteBottomUp___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_mrewriteBottomUp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_mrewriteBottomUp___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_mrewriteBottomUp___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_mrewriteBottomUp(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Syntax_rewriteBottomUp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
lean_inc(x_8);
lean_inc(x_1);
x_12 = l_Lean_Syntax_mrewriteBottomUp___main___at_Lean_Syntax_rewriteBottomUp___spec__1(x_1, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_12;
lean_dec(x_8);
x_16 = lean_array_fset(x_11, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
lean_object* l_Lean_Syntax_mrewriteBottomUp___main___at_Lean_Syntax_rewriteBottomUp___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_6 = l_Array_umapMAux___main___at_Lean_Syntax_rewriteBottomUp___spec__2(x_1, x_5, x_4);
lean_ctor_set(x_2, 1, x_6);
x_7 = lean_apply_1(x_1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_11 = l_Array_umapMAux___main___at_Lean_Syntax_rewriteBottomUp___spec__2(x_1, x_10, x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_apply_1(x_1, x_12);
return x_13;
}
}
else
{
lean_object* x_14; 
x_14 = lean_apply_1(x_1, x_2);
return x_14;
}
}
}
lean_object* l_Lean_Syntax_rewriteBottomUp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_mrewriteBottomUp___main___at_Lean_Syntax_rewriteBottomUp___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Syntax_1__updateInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_4, 2);
lean_dec(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_dec(x_8);
lean_inc(x_6);
lean_ctor_set(x_4, 2, x_6);
lean_ctor_set(x_4, 1, x_2);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_9);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 x_16 = x_12;
} else {
 lean_dec_ref(x_12);
 x_16 = lean_box(0);
}
lean_inc(x_13);
if (lean_is_scalar(x_16)) {
 x_17 = lean_alloc_ctor(0, 3, 0);
} else {
 x_17 = x_16;
}
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_14);
return x_18;
}
}
}
lean_object* l___private_Init_Lean_Syntax_2__updateLeadingAux(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l___private_Init_Lean_Syntax_1__updateInfo(x_9, x_2);
lean_ctor_set(x_3, 0, x_12);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l___private_Init_Lean_Syntax_1__updateInfo(x_15, x_2);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_1, 0, x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_24 = x_3;
} else {
 lean_dec_ref(x_3);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_23, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 2);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l___private_Init_Lean_Syntax_1__updateInfo(x_23, x_2);
if (lean_is_scalar(x_24)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_24;
}
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
}
}
case 3:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_2);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_1);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_1, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_38, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 2);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l___private_Init_Lean_Syntax_1__updateInfo(x_38, x_2);
lean_ctor_set(x_32, 0, x_41);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_32, 0);
lean_inc(x_44);
lean_dec(x_32);
x_45 = lean_ctor_get(x_44, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 2);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l___private_Init_Lean_Syntax_1__updateInfo(x_44, x_2);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_1, 0, x_48);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_1, 1);
x_52 = lean_ctor_get(x_1, 2);
x_53 = lean_ctor_get(x_1, 3);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_1);
x_54 = lean_ctor_get(x_32, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_55 = x_32;
} else {
 lean_dec_ref(x_32);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_54, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 2);
lean_inc(x_57);
lean_dec(x_56);
x_58 = l___private_Init_Lean_Syntax_1__updateInfo(x_54, x_2);
if (lean_is_scalar(x_55)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_55;
}
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_51);
lean_ctor_set(x_60, 2, x_52);
lean_ctor_set(x_60, 3, x_53);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
}
}
default: 
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_1);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_2);
return x_64;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Syntax_updateLeading___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_6 = l_Array_empty___closed__1;
x_7 = x_2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_box(0);
x_11 = x_10;
x_12 = lean_array_fset(x_2, x_1, x_11);
lean_inc(x_9);
x_13 = l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1(x_9, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_1, x_16);
x_18 = x_14;
lean_dec(x_9);
x_19 = lean_array_fset(x_12, x_1, x_18);
lean_dec(x_1);
x_1 = x_17;
x_2 = x_19;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_1);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_1, 1);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l_Array_umapMAux___main___at_Lean_Syntax_updateLeading___spec__2(x_60, x_59, x_2);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_ctor_set(x_1, 1, x_63);
lean_ctor_set(x_61, 0, x_1);
return x_61;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_61, 0);
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_61);
lean_ctor_set(x_1, 1, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_1, 0);
x_68 = lean_ctor_get(x_1, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_1);
x_69 = lean_unsigned_to_nat(0u);
x_70 = l_Array_umapMAux___main___at_Lean_Syntax_updateLeading___spec__2(x_69, x_68, x_2);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_71);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
}
else
{
lean_object* x_76; 
x_76 = lean_box(0);
x_3 = x_76;
goto block_57;
}
block_57:
{
lean_dec(x_3);
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l___private_Init_Lean_Syntax_1__updateInfo(x_9, x_2);
lean_ctor_set(x_4, 0, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l___private_Init_Lean_Syntax_1__updateInfo(x_14, x_2);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_1, 0, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_22 = x_4;
} else {
 lean_dec_ref(x_4);
 x_22 = lean_box(0);
}
x_23 = lean_ctor_get(x_21, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 2);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l___private_Init_Lean_Syntax_1__updateInfo(x_21, x_2);
if (lean_is_scalar(x_22)) {
 x_26 = lean_alloc_ctor(1, 1, 0);
} else {
 x_26 = x_22;
}
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
}
case 3:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_2);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_1);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_1, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_34, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 2);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l___private_Init_Lean_Syntax_1__updateInfo(x_34, x_2);
lean_ctor_set(x_29, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_29, 0);
lean_inc(x_39);
lean_dec(x_29);
x_40 = lean_ctor_get(x_39, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 2);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l___private_Init_Lean_Syntax_1__updateInfo(x_39, x_2);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_1, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_45 = lean_ctor_get(x_1, 1);
x_46 = lean_ctor_get(x_1, 2);
x_47 = lean_ctor_get(x_1, 3);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_1);
x_48 = lean_ctor_get(x_29, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_49 = x_29;
} else {
 lean_dec_ref(x_29);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_48, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 2);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l___private_Init_Lean_Syntax_1__updateInfo(x_48, x_2);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_49;
}
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_45);
lean_ctor_set(x_54, 2, x_46);
lean_ctor_set(x_54, 3, x_47);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
}
}
default: 
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_2);
return x_56;
}
}
}
}
}
lean_object* l_Lean_Syntax_updateLeading(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_updateTrailing___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_dec(x_1);
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_2, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_2, 0);
lean_dec(x_10);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_5, x_11);
lean_dec(x_5);
x_13 = l_Lean_Syntax_inhabited;
x_14 = lean_array_get(x_13, x_4, x_12);
x_15 = l_Lean_Syntax_updateTrailing___main(x_1, x_14);
x_16 = lean_array_set(x_4, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_16);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_5, x_17);
lean_dec(x_5);
x_19 = l_Lean_Syntax_inhabited;
x_20 = lean_array_get(x_19, x_4, x_18);
x_21 = l_Lean_Syntax_updateTrailing___main(x_1, x_20);
x_22 = lean_array_set(x_4, x_18, x_21);
lean_dec(x_18);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
case 2:
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_2, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = l_Lean_SourceInfo_updateTrailing(x_28, x_1);
lean_ctor_set(x_24, 0, x_29);
return x_2;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = l_Lean_SourceInfo_updateTrailing(x_30, x_1);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_2, 0, x_32);
return x_2;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
lean_dec(x_2);
x_34 = lean_ctor_get(x_24, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_35 = x_24;
} else {
 lean_dec_ref(x_24);
 x_35 = lean_box(0);
}
x_36 = l_Lean_SourceInfo_updateTrailing(x_34, x_1);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(1, 1, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
default: 
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_2, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_2);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_2, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = l_Lean_SourceInfo_updateTrailing(x_43, x_1);
lean_ctor_set(x_39, 0, x_44);
return x_2;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
lean_inc(x_45);
lean_dec(x_39);
x_46 = l_Lean_SourceInfo_updateTrailing(x_45, x_1);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_2, 0, x_47);
return x_2;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_2, 1);
x_49 = lean_ctor_get(x_2, 2);
x_50 = lean_ctor_get(x_2, 3);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_2);
x_51 = lean_ctor_get(x_39, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_52 = x_39;
} else {
 lean_dec_ref(x_39);
 x_52 = lean_box(0);
}
x_53 = l_Lean_SourceInfo_updateTrailing(x_51, x_1);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_48);
lean_ctor_set(x_55, 2, x_49);
lean_ctor_set(x_55, 3, x_50);
return x_55;
}
}
}
}
}
}
lean_object* l_Lean_Syntax_updateTrailing(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_updateTrailing___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_findMAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
lean_object* l_Lean_Syntax_getHeadInfo___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_findMAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1(x_3, x_4);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
return x_6;
}
}
}
}
lean_object* l_Array_findMAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findMAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_getHeadInfo___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getHeadInfo___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_getHeadInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getHeadInfo___main(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_getHeadInfo___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getHeadInfo(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_getPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getHeadInfo___main(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
lean_object* l_Lean_Syntax_getPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getPos(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_findRevMAux___main___at_Lean_Syntax_getTailInfo___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
lean_dec(x_2);
x_9 = lean_array_fget(x_1, x_8);
x_10 = l_Lean_Syntax_getTailInfo___main(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
x_2 = x_8;
x_3 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_8);
return x_10;
}
}
}
}
lean_object* l_Lean_Syntax_getTailInfo___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Array_findRevMAux___main___at_Lean_Syntax_getTailInfo___main___spec__1(x_3, x_4, lean_box(0));
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
return x_6;
}
}
}
}
lean_object* l_Array_findRevMAux___main___at_Lean_Syntax_getTailInfo___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findRevMAux___main___at_Lean_Syntax_getTailInfo___main___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_getTailInfo___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_getTailInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo___main(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Syntax_3__updateLast___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
lean_inc(x_1);
x_9 = lean_array_get(x_1, x_2, x_8);
lean_inc(x_3);
x_10 = lean_apply_1(x_3, x_9);
if (lean_obj_tag(x_10) == 0)
{
x_4 = x_8;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_array_set(x_2, x_8, x_13);
lean_dec(x_8);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_array_set(x_2, x_8, x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
return x_18;
}
}
}
lean_object* l___private_Init_Lean_Syntax_3__updateLast___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Syntax_3__updateLast___main___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Syntax_3__updateLast___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Syntax_3__updateLast___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Syntax_3__updateLast(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Syntax_3__updateLast___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Syntax_3__updateLast___main___at_Lean_Syntax_setTailInfoAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_Syntax_inhabited;
x_9 = lean_array_get(x_8, x_2, x_7);
lean_inc(x_1);
x_10 = l_Lean_Syntax_setTailInfoAux___main(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
x_3 = x_7;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_array_set(x_2, x_7, x_13);
lean_dec(x_7);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_array_set(x_2, x_7, x_15);
lean_dec(x_7);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
return x_18;
}
}
}
lean_object* l_Lean_Syntax_setTailInfoAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
case 1:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l___private_Init_Lean_Syntax_3__updateLast___main___at_Lean_Syntax_setTailInfoAux___main___spec__1(x_1, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_free_object(x_2);
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_ctor_set(x_2, 1, x_11);
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_ctor_set(x_2, 1, x_12);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = lean_array_get_size(x_15);
x_17 = l___private_Init_Lean_Syntax_3__updateLast___main___at_Lean_Syntax_setTailInfoAux___main___spec__1(x_1, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_14);
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_19);
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(1, 1, 0);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
case 2:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_2, 0);
lean_dec(x_24);
lean_ctor_set(x_2, 0, x_1);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_2);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
default: 
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_2, 0);
lean_dec(x_30);
lean_ctor_set(x_2, 0, x_1);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_2);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_2, 1);
x_33 = lean_ctor_get(x_2, 2);
x_34 = lean_ctor_get(x_2, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_2);
x_35 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
}
lean_object* l_Lean_Syntax_setTailInfoAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_setTailInfoAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_setTailInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_Lean_Syntax_setTailInfoAux___main(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
}
lean_object* l___private_Init_Lean_Syntax_4__reprintLeaf(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_String_Iterator_HasRepr___closed__2;
x_4 = lean_string_append(x_3, x_2);
x_5 = lean_string_append(x_4, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_6, 2);
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_7, 2);
x_12 = lean_string_utf8_extract(x_9, x_10, x_11);
x_13 = lean_string_append(x_12, x_2);
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
x_16 = lean_ctor_get(x_8, 2);
x_17 = lean_string_utf8_extract(x_14, x_15, x_16);
x_18 = lean_string_append(x_13, x_17);
lean_dec(x_17);
return x_18;
}
}
}
lean_object* l___private_Init_Lean_Syntax_4__reprintLeaf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Syntax_4__reprintLeaf(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_fget(x_2, x_3);
x_9 = l_Lean_Syntax_reprint___main(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_string_append(x_4, x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_12;
goto _start;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_fget(x_2, x_3);
x_9 = l_Lean_Syntax_reprint___main(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_string_dec_eq(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_3, x_14);
lean_dec(x_3);
x_3 = x_15;
goto _start;
}
}
}
}
}
lean_object* _init_l_Lean_Syntax_reprint___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_reprint___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_reprint___main___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_choiceKind;
x_6 = lean_name_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_String_splitAux___main___closed__1;
x_9 = l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__1(x_4, x_4, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Syntax_inhabited;
x_14 = lean_array_get(x_13, x_4, x_11);
x_15 = l_Lean_Syntax_reprint___main(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__2(x_4, x_4, x_18, x_17);
return x_19;
}
}
else
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
case 2:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = l___private_Init_Lean_Syntax_4__reprintLeaf(x_21, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
default: 
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_25, 2);
x_30 = lean_string_utf8_extract(x_27, x_28, x_29);
x_31 = l___private_Init_Lean_Syntax_4__reprintLeaf(x_26, x_30);
lean_dec(x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_Syntax_reprint___main___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_reprint___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_reprint___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_reprint(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_reprint___main(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_reprint___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_reprint(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
x_10 = l_Lean_Syntax_formatStxAux___main(x_1, x_9, x_6);
lean_dec(x_9);
x_11 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__1(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
x_16 = l_Lean_Syntax_formatStxAux___main(x_1, x_15, x_12);
lean_dec(x_15);
x_17 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__1(x_1, x_2, x_13);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 0;
lean_inc(x_2);
lean_inc(x_6);
x_8 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_7);
x_9 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(x_4, x_2);
x_10 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_7);
return x_10;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
x_10 = l_Lean_Syntax_formatStxAux___main(x_1, x_9, x_6);
lean_dec(x_9);
x_11 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__3(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
x_16 = l_Lean_Syntax_formatStxAux___main(x_1, x_15, x_12);
lean_dec(x_15);
x_17 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__3(x_1, x_2, x_13);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
x_10 = l_Lean_Syntax_formatStxAux___main(x_1, x_9, x_6);
lean_dec(x_9);
x_11 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__4(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
x_16 = l_Lean_Syntax_formatStxAux___main(x_1, x_15, x_12);
lean_dec(x_15);
x_17 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__4(x_1, x_2, x_13);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
x_10 = l_Lean_Syntax_formatStxAux___main(x_1, x_9, x_6);
lean_dec(x_9);
x_11 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__5(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
x_16 = l_Lean_Syntax_formatStxAux___main(x_1, x_15, x_12);
lean_dec(x_15);
x_17 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__5(x_1, x_2, x_13);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<missing>");
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_formatStxAux___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Syntax_formatStxAux___main___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_formatStxAux___main___closed__4;
x_2 = l_Lean_Syntax_formatStxAux___main___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("noKind");
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_formatStxAux___main___closed__6;
x_2 = l_Lean_Syntax_formatStxAux___main___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("..");
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_formatStxAux___main___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Syntax_formatStxAux___main___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__12() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Format_sbracket___closed__2;
x_3 = l_Lean_Syntax_formatStxAux___main___closed__10;
x_4 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__13() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Syntax_formatStxAux___main___closed__12;
x_3 = l_Lean_Format_sbracket___closed__3;
x_4 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Format_sbracket___closed__1;
x_2 = l_Lean_Syntax_formatStxAux___main___closed__13;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Syntax_formatStxAux___main___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_formatStxAux___main___closed__14;
x_2 = lean_format_group(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_formatStxAux___main___closed__2;
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_2, x_7);
x_9 = l_Lean_Syntax_formatStxAux___main___closed__8;
x_10 = lean_name_eq(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_Syntax_formatStxAux___main___closed__6;
x_12 = lean_box(0);
x_13 = l_Lean_Name_replacePrefix___main(x_5, x_11, x_12);
x_14 = l_System_FilePath_dirName___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_13);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_17; 
x_17 = lean_nat_dec_lt(x_8, x_8);
lean_dec(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = l_Array_toList___rarg(x_6);
lean_dec(x_6);
x_19 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__1(x_1, x_2, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(1);
x_22 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(x_20, x_21);
lean_dec(x_20);
x_23 = 0;
x_24 = l_Lean_Format_paren___closed__2;
x_25 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_23);
x_26 = l_Lean_Format_paren___closed__3;
x_27 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_23);
x_28 = l_Lean_Format_paren___closed__1;
x_29 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_format_group(x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_6);
x_31 = l_Lean_Syntax_formatStxAux___main___closed__11;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_box(1);
x_34 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(x_32, x_33);
lean_dec(x_32);
x_35 = 0;
x_36 = l_Lean_Format_paren___closed__2;
x_37 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_35);
x_38 = l_Lean_Format_paren___closed__3;
x_39 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_35);
x_40 = l_Lean_Format_paren___closed__1;
x_41 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_format_group(x_41);
return x_42;
}
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_nat_dec_lt(x_43, x_8);
lean_dec(x_8);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_45 = l_Array_toList___rarg(x_6);
lean_dec(x_6);
x_46 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__3(x_1, x_2, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_16);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_box(1);
x_49 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(x_47, x_48);
lean_dec(x_47);
x_50 = 0;
x_51 = l_Lean_Format_paren___closed__2;
x_52 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_50);
x_53 = l_Lean_Format_paren___closed__3;
x_54 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_50);
x_55 = l_Lean_Format_paren___closed__1;
x_56 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_format_group(x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_6);
x_58 = l_Lean_Syntax_formatStxAux___main___closed__11;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_16);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_box(1);
x_61 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(x_59, x_60);
lean_dec(x_59);
x_62 = 0;
x_63 = l_Lean_Format_paren___closed__2;
x_64 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_62);
x_65 = l_Lean_Format_paren___closed__3;
x_66 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*2, x_62);
x_67 = l_Lean_Format_paren___closed__1;
x_68 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_format_group(x_68);
return x_69;
}
}
}
else
{
lean_dec(x_5);
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_70; 
x_70 = lean_nat_dec_lt(x_8, x_8);
lean_dec(x_8);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_71 = l_Array_toList___rarg(x_6);
lean_dec(x_6);
x_72 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__4(x_1, x_2, x_71);
x_73 = lean_box(1);
x_74 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(x_72, x_73);
lean_dec(x_72);
x_75 = 0;
x_76 = l_Lean_Format_sbracket___closed__2;
x_77 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
lean_ctor_set_uint8(x_77, sizeof(void*)*2, x_75);
x_78 = l_Lean_Format_sbracket___closed__3;
x_79 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*2, x_75);
x_80 = l_Lean_Format_sbracket___closed__1;
x_81 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_format_group(x_81);
return x_82;
}
else
{
lean_object* x_83; 
lean_dec(x_6);
x_83 = l_Lean_Syntax_formatStxAux___main___closed__15;
return x_83;
}
}
else
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_1, 0);
x_85 = lean_nat_dec_lt(x_84, x_8);
lean_dec(x_8);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_86 = l_Array_toList___rarg(x_6);
lean_dec(x_6);
x_87 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__5(x_1, x_2, x_86);
x_88 = lean_box(1);
x_89 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(x_87, x_88);
lean_dec(x_87);
x_90 = 0;
x_91 = l_Lean_Format_sbracket___closed__2;
x_92 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
lean_ctor_set_uint8(x_92, sizeof(void*)*2, x_90);
x_93 = l_Lean_Format_sbracket___closed__3;
x_94 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_90);
x_95 = l_Lean_Format_sbracket___closed__1;
x_96 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_format_group(x_96);
return x_97;
}
else
{
lean_object* x_98; 
lean_dec(x_6);
x_98 = l_Lean_Syntax_formatStxAux___main___closed__15;
return x_98;
}
}
}
}
case 2:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_3, 1);
lean_inc(x_99);
lean_dec(x_3);
x_100 = l_String_quote(x_99);
x_101 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
default: 
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_3, 2);
lean_inc(x_102);
lean_dec(x_3);
x_103 = l_System_FilePath_dirName___closed__1;
x_104 = l_Lean_Name_toStringWithSep___main(x_103, x_102);
x_105 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = 0;
x_107 = l_Lean_formatDataValue___closed__2;
x_108 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
lean_ctor_set_uint8(x_108, sizeof(void*)*2, x_106);
return x_108;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStxAux___main___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__4(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___main___at_Lean_Syntax_formatStxAux___main___spec__5(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_formatStxAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_formatStxAux___main(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_formatStxAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_formatStxAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_formatStxAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_formatStxAux(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_formatStx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Syntax_formatStxAux___main(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_formatStx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_formatStx(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_Lean_HasFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Syntax_formatStxAux___main(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_HasToString___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Syntax_formatStxAux___main(x_2, x_3, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Syntax_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_HasToString___lambda__1), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_HasToString___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_HasRepr___closed__1;
x_2 = l_Lean_Syntax_HasToString___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Syntax_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Syntax_HasToString___closed__2;
return x_1;
}
}
lean_object* l_Lean_SyntaxNode_getIdAt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Syntax_inhabited;
x_5 = lean_array_get(x_4, x_3, x_2);
x_6 = l_Lean_Syntax_getId(x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SyntaxNode_getIdAt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* lean_mk_syntax_atom(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* lean_mk_syntax_ident(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_box(0);
x_3 = l_System_FilePath_dirName___closed__1;
lean_inc(x_1);
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_1);
x_5 = lean_string_utf8_byte_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_8);
return x_9;
}
}
lean_object* lean_mk_syntax_list(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_nullKind;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_mkAtom(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_mkNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkNullNode(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_nullKind;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_mkOptionalNode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Lean_mkOptionalNode(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_asNode___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_mkOptionalNode___closed__1;
x_5 = lean_array_push(x_4, x_3);
x_6 = l_Lean_nullKind;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
lean_object* l_Lean_mkStxLit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
x_5 = l_Lean_mkOptionalNode___closed__1;
x_6 = lean_array_push(x_5, x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* l_Lean_mkStxStrLit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_String_quote(x_1);
x_4 = l_Lean_strLitKind;
x_5 = l_Lean_mkStxLit(x_4, x_3, x_2);
return x_5;
}
}
lean_object* l_Lean_mkStxNumLit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_numLitKind;
x_4 = l_Lean_mkStxLit(x_3, x_1, x_2);
return x_4;
}
}
lean_object* lean_mk_syntax_str_lit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_mkStxStrLit(x_1, x_2);
return x_3;
}
}
lean_object* lean_mk_syntax_num_lit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Nat_repr(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_numLitKind;
x_5 = l_Lean_mkStxLit(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Syntax_5__decodeBinLitAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_1, x_2);
if (x_4 == 0)
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_string_utf8_get(x_1, x_2);
x_6 = 48;
x_7 = x_5 == x_6;
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 49;
x_9 = x_5 == x_8;
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_mul(x_12, x_3);
lean_dec(x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_13, x_14);
lean_dec(x_13);
x_2 = x_11;
x_3 = x_15;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_nat_mul(x_18, x_3);
lean_dec(x_3);
x_2 = x_17;
x_3 = x_19;
goto _start;
}
}
else
{
lean_object* x_21; 
lean_dec(x_2);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_3);
return x_21;
}
}
}
lean_object* l___private_Init_Lean_Syntax_5__decodeBinLitAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Syntax_5__decodeBinLitAux___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Syntax_5__decodeBinLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Syntax_5__decodeBinLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Syntax_5__decodeBinLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Syntax_5__decodeBinLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Syntax_6__decodeOctalLitAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_1, x_2);
if (x_4 == 0)
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_string_utf8_get(x_1, x_2);
x_6 = 48;
x_7 = x_6 <= x_5;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(0);
return x_8;
}
else
{
uint32_t x_9; uint8_t x_10; 
x_9 = 55;
x_10 = x_5 <= x_9;
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_13 = lean_unsigned_to_nat(8u);
x_14 = lean_nat_mul(x_13, x_3);
lean_dec(x_3);
x_15 = lean_uint32_to_nat(x_5);
x_16 = lean_nat_add(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(48u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_2 = x_12;
x_3 = x_18;
goto _start;
}
}
}
else
{
lean_object* x_20; 
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
}
}
lean_object* l___private_Init_Lean_Syntax_6__decodeOctalLitAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Syntax_6__decodeOctalLitAux___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Syntax_6__decodeOctalLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Syntax_6__decodeOctalLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Syntax_6__decodeOctalLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Syntax_6__decodeOctalLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Syntax_7__decodeHexDigit(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; uint32_t x_44; uint8_t x_45; 
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = lean_string_utf8_next(x_1, x_2);
x_44 = 48;
x_45 = x_44 <= x_3;
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_box(0);
x_5 = x_46;
goto block_43;
}
else
{
uint32_t x_47; uint8_t x_48; 
x_47 = 57;
x_48 = x_3 <= x_47;
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_box(0);
x_5 = x_49;
goto block_43;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_uint32_to_nat(x_3);
x_51 = lean_unsigned_to_nat(48u);
x_52 = lean_nat_sub(x_50, x_51);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_4);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
block_43:
{
uint32_t x_6; uint8_t x_7; 
lean_dec(x_5);
x_6 = 97;
x_7 = x_6 <= x_3;
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 65;
x_9 = x_8 <= x_3;
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_box(0);
return x_10;
}
else
{
uint32_t x_11; uint8_t x_12; 
x_11 = 70;
x_12 = x_3 <= x_11;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_uint32_to_nat(x_3);
x_15 = lean_unsigned_to_nat(10u);
x_16 = lean_nat_add(x_15, x_14);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(65u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint32_t x_21; uint8_t x_22; 
x_21 = 102;
x_22 = x_3 <= x_21;
if (x_22 == 0)
{
uint32_t x_23; uint8_t x_24; 
x_23 = 65;
x_24 = x_23 <= x_3;
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_4);
x_25 = lean_box(0);
return x_25;
}
else
{
uint32_t x_26; uint8_t x_27; 
x_26 = 70;
x_27 = x_3 <= x_26;
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_4);
x_28 = lean_box(0);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_uint32_to_nat(x_3);
x_30 = lean_unsigned_to_nat(10u);
x_31 = lean_nat_add(x_30, x_29);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(65u);
x_33 = lean_nat_sub(x_31, x_32);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_uint32_to_nat(x_3);
x_37 = lean_unsigned_to_nat(10u);
x_38 = lean_nat_add(x_37, x_36);
lean_dec(x_36);
x_39 = lean_unsigned_to_nat(97u);
x_40 = lean_nat_sub(x_38, x_39);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_4);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
}
lean_object* l___private_Init_Lean_Syntax_7__decodeHexDigit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Syntax_7__decodeHexDigit(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Syntax_8__decodeHexLitAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Syntax_7__decodeHexDigit(x_1, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(16u);
x_11 = lean_nat_mul(x_10, x_3);
lean_dec(x_3);
x_12 = lean_nat_add(x_11, x_8);
lean_dec(x_8);
lean_dec(x_11);
x_2 = x_9;
x_3 = x_12;
goto _start;
}
}
else
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_3);
return x_14;
}
}
}
lean_object* l___private_Init_Lean_Syntax_8__decodeHexLitAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Syntax_8__decodeHexLitAux___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Syntax_8__decodeHexLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Syntax_8__decodeHexLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Syntax_8__decodeHexLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Syntax_8__decodeHexLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Syntax_9__decodeDecimalLitAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_1, x_2);
if (x_4 == 0)
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_string_utf8_get(x_1, x_2);
x_6 = 48;
x_7 = x_6 <= x_5;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(0);
return x_8;
}
else
{
uint32_t x_9; uint8_t x_10; 
x_9 = 57;
x_10 = x_5 <= x_9;
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_13 = lean_unsigned_to_nat(10u);
x_14 = lean_nat_mul(x_13, x_3);
lean_dec(x_3);
x_15 = lean_uint32_to_nat(x_5);
x_16 = lean_nat_add(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(48u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_2 = x_12;
x_3 = x_18;
goto _start;
}
}
}
else
{
lean_object* x_20; 
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
}
}
lean_object* l___private_Init_Lean_Syntax_9__decodeDecimalLitAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Syntax_9__decodeDecimalLitAux___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Syntax_9__decodeDecimalLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Syntax_9__decodeDecimalLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Syntax_9__decodeDecimalLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Syntax_9__decodeDecimalLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_Syntax_10__decodeNatLitVal___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Syntax_10__decodeNatLitVal(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_string_length(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_string_utf8_get(x_1, x_3);
x_6 = 48;
x_7 = x_5 == x_6;
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = l_Char_isDigit(x_5);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Syntax_9__decodeDecimalLitAux___main(x_1, x_3, x_3);
return x_10;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_dec_eq(x_2, x_11);
lean_dec(x_2);
if (x_12 == 0)
{
uint32_t x_13; uint32_t x_14; uint8_t x_15; 
x_13 = lean_string_utf8_get(x_1, x_11);
x_14 = 120;
x_15 = x_13 == x_14;
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 88;
x_17 = x_13 == x_16;
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; uint8_t x_38; 
x_18 = 98;
x_38 = x_13 == x_18;
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = 0;
x_19 = x_39;
goto block_37;
}
else
{
uint8_t x_40; 
x_40 = 1;
x_19 = x_40;
goto block_37;
}
block_37:
{
if (x_19 == 0)
{
uint32_t x_20; uint8_t x_21; 
x_20 = 66;
x_21 = x_13 == x_20;
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 111;
x_23 = x_13 == x_22;
if (x_23 == 0)
{
uint32_t x_24; uint8_t x_25; 
x_24 = 79;
x_25 = x_13 == x_24;
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Char_isDigit(x_13);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_box(0);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = l___private_Init_Lean_Syntax_9__decodeDecimalLitAux___main(x_1, x_3, x_3);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_unsigned_to_nat(2u);
x_30 = l___private_Init_Lean_Syntax_6__decodeOctalLitAux___main(x_1, x_29, x_3);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_unsigned_to_nat(2u);
x_32 = l___private_Init_Lean_Syntax_6__decodeOctalLitAux___main(x_1, x_31, x_3);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_unsigned_to_nat(2u);
x_34 = l___private_Init_Lean_Syntax_5__decodeBinLitAux___main(x_1, x_33, x_3);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_unsigned_to_nat(2u);
x_36 = l___private_Init_Lean_Syntax_5__decodeBinLitAux___main(x_1, x_35, x_3);
return x_36;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_unsigned_to_nat(2u);
x_42 = l___private_Init_Lean_Syntax_8__decodeHexLitAux___main(x_1, x_41, x_3);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_unsigned_to_nat(2u);
x_44 = l___private_Init_Lean_Syntax_8__decodeHexLitAux___main(x_1, x_43, x_3);
return x_44;
}
}
else
{
lean_object* x_45; 
x_45 = l___private_Init_Lean_Syntax_10__decodeNatLitVal___closed__1;
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_2);
x_46 = lean_box(0);
return x_46;
}
}
}
lean_object* l___private_Init_Lean_Syntax_10__decodeNatLitVal___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Syntax_10__decodeNatLitVal(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_isNatLitAux(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_name_eq(x_3, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Syntax_inhabited;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_11, x_4, x_12);
if (lean_obj_tag(x_13) == 2)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l___private_Init_Lean_Syntax_10__decodeNatLitVal(x_14);
lean_dec(x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_13);
x_16 = lean_box(0);
return x_16;
}
}
}
}
else
{
lean_object* x_17; 
x_17 = lean_box(0);
return x_17;
}
}
}
lean_object* l_Lean_Syntax_isNatLitAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_isNatLitAux(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_numLitKind;
x_3 = l_Lean_Syntax_isNatLitAux(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isNatLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_fieldIdxKind;
x_3 = l_Lean_Syntax_isNatLitAux(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isFieldIdx_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
case 3:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_string_utf8_extract(x_5, x_6, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
default: 
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
}
}
}
lean_object* l_Lean_Syntax_isIdOrAtom_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isIdOrAtom_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_toNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_numLitKind;
x_3 = l_Lean_Syntax_isNatLitAux(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
return x_5;
}
}
}
lean_object* l_Lean_Syntax_toNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_toNat(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 9;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__3() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 39;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__4() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 34;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__5() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 92;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Syntax_11__decodeQuotedChar(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; uint32_t x_5; uint8_t x_6; 
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = lean_string_utf8_next(x_1, x_2);
x_5 = 92;
x_6 = x_3 == x_5;
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 34;
x_8 = x_3 == x_7;
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 39;
x_10 = x_3 == x_9;
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 110;
x_12 = x_3 == x_11;
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 116;
x_14 = x_3 == x_13;
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 120;
x_16 = x_3 == x_15;
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 117;
x_18 = x_3 == x_17;
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_4);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = l___private_Init_Lean_Syntax_7__decodeHexDigit(x_1, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_box(0);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Init_Lean_Syntax_7__decodeHexDigit(x_1, x_24);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec(x_23);
x_26 = lean_box(0);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l___private_Init_Lean_Syntax_7__decodeHexDigit(x_1, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec(x_28);
lean_dec(x_23);
x_31 = lean_box(0);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l___private_Init_Lean_Syntax_7__decodeHexDigit(x_1, x_34);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_23);
x_36 = lean_box(0);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint32_t x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_unsigned_to_nat(16u);
x_42 = lean_nat_mul(x_41, x_23);
lean_dec(x_23);
x_43 = lean_nat_add(x_42, x_28);
lean_dec(x_28);
lean_dec(x_42);
x_44 = lean_nat_mul(x_41, x_43);
lean_dec(x_43);
x_45 = lean_nat_add(x_44, x_33);
lean_dec(x_33);
lean_dec(x_44);
x_46 = lean_nat_mul(x_41, x_45);
lean_dec(x_45);
x_47 = lean_nat_add(x_46, x_40);
lean_dec(x_40);
lean_dec(x_46);
x_48 = l_Char_ofNat(x_47);
lean_dec(x_47);
x_49 = lean_box_uint32(x_48);
lean_ctor_set(x_38, 0, x_49);
return x_35;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint32_t x_59; lean_object* x_60; lean_object* x_61; 
x_50 = lean_ctor_get(x_38, 0);
x_51 = lean_ctor_get(x_38, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_38);
x_52 = lean_unsigned_to_nat(16u);
x_53 = lean_nat_mul(x_52, x_23);
lean_dec(x_23);
x_54 = lean_nat_add(x_53, x_28);
lean_dec(x_28);
lean_dec(x_53);
x_55 = lean_nat_mul(x_52, x_54);
lean_dec(x_54);
x_56 = lean_nat_add(x_55, x_33);
lean_dec(x_33);
lean_dec(x_55);
x_57 = lean_nat_mul(x_52, x_56);
lean_dec(x_56);
x_58 = lean_nat_add(x_57, x_50);
lean_dec(x_50);
lean_dec(x_57);
x_59 = l_Char_ofNat(x_58);
lean_dec(x_58);
x_60 = lean_box_uint32(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_51);
lean_ctor_set(x_35, 0, x_61);
return x_35;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint32_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
lean_dec(x_35);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_unsigned_to_nat(16u);
x_67 = lean_nat_mul(x_66, x_23);
lean_dec(x_23);
x_68 = lean_nat_add(x_67, x_28);
lean_dec(x_28);
lean_dec(x_67);
x_69 = lean_nat_mul(x_66, x_68);
lean_dec(x_68);
x_70 = lean_nat_add(x_69, x_33);
lean_dec(x_33);
lean_dec(x_69);
x_71 = lean_nat_mul(x_66, x_70);
lean_dec(x_70);
x_72 = lean_nat_add(x_71, x_63);
lean_dec(x_63);
lean_dec(x_71);
x_73 = l_Char_ofNat(x_72);
lean_dec(x_72);
x_74 = lean_box_uint32(x_73);
if (lean_is_scalar(x_65)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_65;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_64);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
}
}
}
}
else
{
lean_object* x_77; 
x_77 = l___private_Init_Lean_Syntax_7__decodeHexDigit(x_1, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_box(0);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l___private_Init_Lean_Syntax_7__decodeHexDigit(x_1, x_81);
lean_dec(x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
lean_dec(x_80);
x_83 = lean_box(0);
return x_83;
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint32_t x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_unsigned_to_nat(16u);
x_89 = lean_nat_mul(x_88, x_80);
lean_dec(x_80);
x_90 = lean_nat_add(x_89, x_87);
lean_dec(x_87);
lean_dec(x_89);
x_91 = l_Char_ofNat(x_90);
lean_dec(x_90);
x_92 = lean_box_uint32(x_91);
lean_ctor_set(x_85, 0, x_92);
return x_82;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint32_t x_98; lean_object* x_99; lean_object* x_100; 
x_93 = lean_ctor_get(x_85, 0);
x_94 = lean_ctor_get(x_85, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_85);
x_95 = lean_unsigned_to_nat(16u);
x_96 = lean_nat_mul(x_95, x_80);
lean_dec(x_80);
x_97 = lean_nat_add(x_96, x_93);
lean_dec(x_93);
lean_dec(x_96);
x_98 = l_Char_ofNat(x_97);
lean_dec(x_97);
x_99 = lean_box_uint32(x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_94);
lean_ctor_set(x_82, 0, x_100);
return x_82;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint32_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_101 = lean_ctor_get(x_82, 0);
lean_inc(x_101);
lean_dec(x_82);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = lean_unsigned_to_nat(16u);
x_106 = lean_nat_mul(x_105, x_80);
lean_dec(x_80);
x_107 = lean_nat_add(x_106, x_102);
lean_dec(x_102);
lean_dec(x_106);
x_108 = l_Char_ofNat(x_107);
lean_dec(x_107);
x_109 = lean_box_uint32(x_108);
if (lean_is_scalar(x_104)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_104;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_103);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__1;
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_4);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__2;
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_4);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__3;
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_4);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__4;
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_4);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__5;
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_4);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
lean_object* l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Syntax_11__decodeQuotedChar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_decodeStrLitAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_4 = lean_string_utf8_get(x_1, x_2);
x_5 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_6 = 34;
x_7 = x_4 == x_6;
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 92;
x_9 = x_4 == x_8;
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_string_push(x_3, x_4);
x_2 = x_5;
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = l___private_Init_Lean_Syntax_11__decodeQuotedChar(x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unbox_uint32(x_15);
lean_dec(x_15);
x_18 = lean_string_push(x_3, x_17);
x_2 = x_16;
x_3 = x_18;
goto _start;
}
}
}
else
{
lean_object* x_20; 
lean_dec(x_5);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
}
}
lean_object* l_Lean_Syntax_decodeStrLitAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_decodeStrLitAux___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_decodeStrLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_decodeStrLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_decodeStrLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_decodeStrLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_String_splitAux___main___closed__1;
x_4 = l_Lean_Syntax_decodeStrLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_decodeStrLit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_decodeStrLit(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_strLitKind;
x_5 = lean_name_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Syntax_inhabited;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_11, x_3, x_12);
if (lean_obj_tag(x_13) == 2)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_String_splitAux___main___closed__1;
x_16 = l_Lean_Syntax_decodeStrLitAux___main(x_14, x_8, x_15);
lean_dec(x_14);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_13);
x_17 = lean_box(0);
return x_17;
}
}
}
}
else
{
lean_object* x_18; 
x_18 = lean_box(0);
return x_18;
}
}
}
lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isStrLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_decodeCharLit(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 92;
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box_uint32(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(2u);
x_9 = l___private_Init_Lean_Syntax_11__decodeQuotedChar(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
}
lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_decodeCharLit(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_charLitKind;
x_5 = lean_name_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Syntax_inhabited;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_11, x_3, x_12);
if (lean_obj_tag(x_13) == 2)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Syntax_decodeCharLit(x_14);
lean_dec(x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_13);
x_16 = lean_box(0);
return x_16;
}
}
}
}
else
{
lean_object* x_17; 
x_17 = lean_box(0);
return x_17;
}
}
}
lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isCharLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_Syntax_hasArgs(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
lean_dec(x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_hasArgs(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_mkIdentFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l_Lean_Syntax_getHeadInfo___main(x_1);
x_4 = l_System_FilePath_dirName___closed__1;
lean_inc(x_2);
x_5 = l_Lean_Name_toStringWithSep___main(x_4, x_2);
x_6 = lean_string_utf8_byte_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_6);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_2);
lean_ctor_set(x_10, 3, x_9);
return x_10;
}
}
lean_object* l_Lean_mkIdentFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkIdentFrom(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_mkAtomFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_getHeadInfo___main(x_1);
x_4 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_mkAtomFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkAtomFrom(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_Data_Array(lean_object*);
lean_object* initialize_Init_Lean_Data_Name(lean_object*);
lean_object* initialize_Init_Lean_Data_Format(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Syntax(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Data_Name(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Data_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_choiceKind___closed__1 = _init_l_Lean_choiceKind___closed__1();
lean_mark_persistent(l_Lean_choiceKind___closed__1);
l_Lean_choiceKind___closed__2 = _init_l_Lean_choiceKind___closed__2();
lean_mark_persistent(l_Lean_choiceKind___closed__2);
l_Lean_choiceKind = _init_l_Lean_choiceKind();
lean_mark_persistent(l_Lean_choiceKind);
l_Lean_nullKind___closed__1 = _init_l_Lean_nullKind___closed__1();
lean_mark_persistent(l_Lean_nullKind___closed__1);
l_Lean_nullKind___closed__2 = _init_l_Lean_nullKind___closed__2();
lean_mark_persistent(l_Lean_nullKind___closed__2);
l_Lean_nullKind = _init_l_Lean_nullKind();
lean_mark_persistent(l_Lean_nullKind);
l_Lean_strLitKind___closed__1 = _init_l_Lean_strLitKind___closed__1();
lean_mark_persistent(l_Lean_strLitKind___closed__1);
l_Lean_strLitKind___closed__2 = _init_l_Lean_strLitKind___closed__2();
lean_mark_persistent(l_Lean_strLitKind___closed__2);
l_Lean_strLitKind = _init_l_Lean_strLitKind();
lean_mark_persistent(l_Lean_strLitKind);
l_Lean_charLitKind___closed__1 = _init_l_Lean_charLitKind___closed__1();
lean_mark_persistent(l_Lean_charLitKind___closed__1);
l_Lean_charLitKind___closed__2 = _init_l_Lean_charLitKind___closed__2();
lean_mark_persistent(l_Lean_charLitKind___closed__2);
l_Lean_charLitKind = _init_l_Lean_charLitKind();
lean_mark_persistent(l_Lean_charLitKind);
l_Lean_numLitKind___closed__1 = _init_l_Lean_numLitKind___closed__1();
lean_mark_persistent(l_Lean_numLitKind___closed__1);
l_Lean_numLitKind___closed__2 = _init_l_Lean_numLitKind___closed__2();
lean_mark_persistent(l_Lean_numLitKind___closed__2);
l_Lean_numLitKind = _init_l_Lean_numLitKind();
lean_mark_persistent(l_Lean_numLitKind);
l_Lean_fieldIdxKind___closed__1 = _init_l_Lean_fieldIdxKind___closed__1();
lean_mark_persistent(l_Lean_fieldIdxKind___closed__1);
l_Lean_fieldIdxKind___closed__2 = _init_l_Lean_fieldIdxKind___closed__2();
lean_mark_persistent(l_Lean_fieldIdxKind___closed__2);
l_Lean_fieldIdxKind = _init_l_Lean_fieldIdxKind();
lean_mark_persistent(l_Lean_fieldIdxKind);
l_Lean_Syntax_asNode___closed__1 = _init_l_Lean_Syntax_asNode___closed__1();
lean_mark_persistent(l_Lean_Syntax_asNode___closed__1);
l_Lean_Syntax_reprint___main___closed__1 = _init_l_Lean_Syntax_reprint___main___closed__1();
lean_mark_persistent(l_Lean_Syntax_reprint___main___closed__1);
l_Lean_Syntax_formatStxAux___main___closed__1 = _init_l_Lean_Syntax_formatStxAux___main___closed__1();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__1);
l_Lean_Syntax_formatStxAux___main___closed__2 = _init_l_Lean_Syntax_formatStxAux___main___closed__2();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__2);
l_Lean_Syntax_formatStxAux___main___closed__3 = _init_l_Lean_Syntax_formatStxAux___main___closed__3();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__3);
l_Lean_Syntax_formatStxAux___main___closed__4 = _init_l_Lean_Syntax_formatStxAux___main___closed__4();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__4);
l_Lean_Syntax_formatStxAux___main___closed__5 = _init_l_Lean_Syntax_formatStxAux___main___closed__5();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__5);
l_Lean_Syntax_formatStxAux___main___closed__6 = _init_l_Lean_Syntax_formatStxAux___main___closed__6();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__6);
l_Lean_Syntax_formatStxAux___main___closed__7 = _init_l_Lean_Syntax_formatStxAux___main___closed__7();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__7);
l_Lean_Syntax_formatStxAux___main___closed__8 = _init_l_Lean_Syntax_formatStxAux___main___closed__8();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__8);
l_Lean_Syntax_formatStxAux___main___closed__9 = _init_l_Lean_Syntax_formatStxAux___main___closed__9();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__9);
l_Lean_Syntax_formatStxAux___main___closed__10 = _init_l_Lean_Syntax_formatStxAux___main___closed__10();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__10);
l_Lean_Syntax_formatStxAux___main___closed__11 = _init_l_Lean_Syntax_formatStxAux___main___closed__11();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__11);
l_Lean_Syntax_formatStxAux___main___closed__12 = _init_l_Lean_Syntax_formatStxAux___main___closed__12();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__12);
l_Lean_Syntax_formatStxAux___main___closed__13 = _init_l_Lean_Syntax_formatStxAux___main___closed__13();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__13);
l_Lean_Syntax_formatStxAux___main___closed__14 = _init_l_Lean_Syntax_formatStxAux___main___closed__14();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__14);
l_Lean_Syntax_formatStxAux___main___closed__15 = _init_l_Lean_Syntax_formatStxAux___main___closed__15();
lean_mark_persistent(l_Lean_Syntax_formatStxAux___main___closed__15);
l_Lean_Syntax_HasToString___closed__1 = _init_l_Lean_Syntax_HasToString___closed__1();
lean_mark_persistent(l_Lean_Syntax_HasToString___closed__1);
l_Lean_Syntax_HasToString___closed__2 = _init_l_Lean_Syntax_HasToString___closed__2();
lean_mark_persistent(l_Lean_Syntax_HasToString___closed__2);
l_Lean_Syntax_HasToString = _init_l_Lean_Syntax_HasToString();
lean_mark_persistent(l_Lean_Syntax_HasToString);
l_Lean_mkOptionalNode___closed__1 = _init_l_Lean_mkOptionalNode___closed__1();
lean_mark_persistent(l_Lean_mkOptionalNode___closed__1);
l___private_Init_Lean_Syntax_10__decodeNatLitVal___closed__1 = _init_l___private_Init_Lean_Syntax_10__decodeNatLitVal___closed__1();
lean_mark_persistent(l___private_Init_Lean_Syntax_10__decodeNatLitVal___closed__1);
l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__1 = _init_l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__1();
lean_mark_persistent(l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__1);
l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__2 = _init_l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__2();
lean_mark_persistent(l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__2);
l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__3 = _init_l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__3();
lean_mark_persistent(l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__3);
l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__4 = _init_l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__4();
lean_mark_persistent(l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__4);
l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__5 = _init_l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__5();
lean_mark_persistent(l___private_Init_Lean_Syntax_11__decodeQuotedChar___boxed__const__5);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
