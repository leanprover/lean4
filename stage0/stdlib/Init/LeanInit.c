// Lean compiler output
// Module: Init.LeanInit
// Imports: Init.Data.String.Basic Init.Data.Array.Basic Init.Data.UInt Init.Data.Hashable Init.Control.Reader Init.Control.EState
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Array_getSepElems___rarg___boxed(lean_object*);
lean_object* l_Lean_mkTermId(lean_object*);
lean_object* l_Lean_mkHole___closed__3;
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*);
lean_object* l_Lean_mkCTermIdFrom___boxed(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l___private_Init_LeanInit_9__decodeHexLitAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Syntax_isIdOrAtom_x3f___boxed(lean_object*);
lean_object* l_Lean_mkAppStx(lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_ParserDescr_pushLeading;
lean_object* l_Lean_fieldIdxKind;
lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object*);
lean_object* l_Lean_MacroM_monadQuotation;
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__1;
lean_object* l___private_Init_LeanInit_10__decodeDecimalLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkTermIdFromIdent(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_nullKind;
lean_object* l_Lean_Name_HasAppend;
lean_object* l_Lean_Syntax_identToAtom___boxed(lean_object*);
lean_object* l_Lean_fieldIdxKind___closed__2;
lean_object* l_Lean_ParserDescr_orelse(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MacroM_monadQuotation___lambda__2(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_3__extractMainModule(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_8__decodeHexDigit___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_10__decodeDecimalLitAux___main(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_optional(uint8_t, lean_object*);
lean_object* l_Lean_Syntax_toNat___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_8__decodeHexDigit(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_lookahead(uint8_t, lean_object*);
lean_object* l___private_Init_LeanInit_4__extractMacroScopesAux(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Syntax_isOfKind___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_HasBeq;
lean_object* l_Lean_fieldIdxKind___closed__1;
uint8_t l_Char_isDigit(uint32_t);
lean_object* l_Lean_charLitKind___closed__2;
lean_object* l___private_Init_LeanInit_1__mkMacroScopeName(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_many(uint8_t, lean_object*);
lean_object* l___private_Init_LeanInit_7__decodeOctalLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_ident(uint8_t);
lean_object* l___private_Init_LeanInit_9__decodeHexLitAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_HasToString___closed__1;
lean_object* l_Lean_mkNameSimple(lean_object*);
lean_object* l_Lean_mkHole___boxed(lean_object*);
lean_object* l_Lean_ParserDescr_andthen___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_char(uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_charLitKind___closed__1;
lean_object* l___private_Init_LeanInit_6__decodeBinLitAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_termIdToAntiquot___closed__3;
lean_object* l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__4;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_inhabited;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Syntax_identToStrLit(lean_object*);
lean_object* l___private_Init_LeanInit_6__decodeBinLitAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_termIdToAntiquot___closed__1;
lean_object* l___private_Init_LeanInit_12__decodeQuotedChar___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hashable___closed__1;
lean_object* l___private_Init_LeanInit_2__assembleExtractedName(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo___main___boxed(lean_object*);
lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l_Lean_mkIdentFrom___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_2__assembleExtractedName___main(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeStrLitAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameGenerator_Inhabited;
lean_object* l_Lean_mkTermIdFromIdent___closed__1;
lean_object* l_Lean_ParserDescr_try(uint8_t, lean_object*);
lean_object* l_Lean_Syntax_termIdToAntiquot___closed__2;
lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l_Lean_mkAppStx___closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1(lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind___closed__2;
lean_object* l_Lean_Syntax_getKind___closed__1;
lean_object* l_Lean_Name_hashable;
lean_object* l_Lean_mkTermIdFromIdent___closed__2;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_str(uint8_t);
lean_object* l_Lean_Syntax_strLitToAtom(lean_object*);
lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object*);
lean_object* l_Lean_mkStxNumLit(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescrCore_inhabited(uint8_t);
lean_object* l_Lean_Name_HasAppend___closed__1;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_MacroM_monadQuotation___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind___closed__4;
lean_object* l_Lean_Syntax_termIdToAntiquot___closed__4;
lean_object* l_Lean_ParserDescr_many1(uint8_t, lean_object*);
lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_6__decodeBinLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_numLitKind;
lean_object* l_Lean_ParserDescr_many___boxed(lean_object*, lean_object*);
lean_object* l_Lean_choiceKind___closed__1;
lean_object* l___private_Init_LeanInit_7__decodeOctalLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_choiceKind___closed__2;
lean_object* l_Lean_Macro_mkFreshName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_num___boxed(lean_object*);
lean_object* l_Lean_MacroM_monadQuotation___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_strLitKind;
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Lean_Macro_mkFreshName(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_getSepElems(lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object*);
lean_object* l_Lean_ParserDescr_many1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkTermIdFrom___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_numLitKind___closed__1;
lean_object* l_Lean_NameGenerator_next(lean_object*);
lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object*);
lean_object* l_Lean_strLitKind___closed__1;
lean_object* l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__5;
lean_object* l_Lean_Syntax_isNatLitAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_NameGenerator_Inhabited___closed__2;
lean_object* l_Lean_Syntax_getArgs___boxed(lean_object*);
lean_object* l_Array_getSepElems___rarg(lean_object*);
lean_object* l___private_Init_LeanInit_10__decodeDecimalLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNullNode(lean_object*);
lean_object* l_Lean_strLitKind___closed__2;
lean_object* l_Lean_NameGenerator_Inhabited___closed__1;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_ParserDescr_parser(uint8_t, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Name_HasToString;
lean_object* l_Lean_ParserDescr_lookahead___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_sepBy(uint8_t, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_choiceKind;
lean_object* l_Lean_charLitKind;
lean_object* l_Lean_ParserDescr_andthen(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_6__decodeBinLitAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_symbol___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_9__decodeHexLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_5__eraseMacroScopesAux___main___boxed(lean_object*);
lean_object* l_Lean_numLitKind___closed__2;
lean_object* l_Lean_ParserDescr_node(uint8_t, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l_Lean_ParserDescr_try___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_ident___boxed(lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_Lean_ParserDescr_str___boxed(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ExtractMacroScopesResult_inhabited___closed__1;
lean_object* l_Lean_ParserDescr_node___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameGenerator_mkChild(lean_object*);
lean_object* l_Lean_ParserDescr_parser___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_nullKind___closed__1;
lean_object* l_Lean_Syntax_decodeStrLit___boxed(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_nonReservedSymbol___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeCharLit(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_7__decodeOctalLitAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_MacroM_monadQuotation___closed__3;
lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_5__eraseMacroScopesAux___boxed(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main___closed__1;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo___main(lean_object*);
lean_object* l___private_Init_LeanInit_5__eraseMacroScopesAux(lean_object*);
lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object*);
lean_object* l_Lean_ParserDescrCore_inhabited___boxed(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes___main(lean_object*);
lean_object* l_Lean_ParserDescr_sepBy1(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkCTermId(lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_Syntax_inhabited;
lean_object* l_Lean_mkAppStx___closed__5;
lean_object* l_Lean_mkHole(lean_object*);
lean_object* l_Lean_MacroM_monadQuotation___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_char___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_4__extractMacroScopesAux___main(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_hasArgs(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l___private_Init_LeanInit_12__decodeQuotedChar(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Syntax_getArg___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_3__extractMainModule___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_identToAtom(lean_object*);
lean_object* l_Lean_Name_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_11__decodeNatLitVal___boxed(lean_object*);
lean_object* l_Lean_ExtractMacroScopesResult_inhabited;
lean_object* l___private_Init_LeanInit_11__decodeNatLitVal___closed__1;
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l___private_Init_LeanInit_7__decodeOctalLitAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameGenerator_curr(lean_object*);
lean_object* l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__2;
lean_object* l_Lean_mkHole___closed__1;
lean_object* l_Lean_Name_hasMacroScopes___boxed(lean_object*);
lean_object* l_Lean_mkStxStrLit(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScopes(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCAppStx(lean_object*, lean_object*);
lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Name_HasBeq___closed__1;
lean_object* l_Lean_Name_append___main___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_5__eraseMacroScopesAux___main(lean_object*);
lean_object* l_Lean_mkTermIdFrom(lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_ParserDescr_orelse___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_10__decodeDecimalLitAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_termIdToAntiquot(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeStrLit(lean_object*);
lean_object* l___private_Init_LeanInit_1__mkMacroScopeName___closed__1;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
size_t lean_usize_mix_hash(size_t, size_t);
lean_object* l_Lean_mkCIdentFrom___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkHole___closed__2;
lean_object* l_Lean_mkCIdentFrom___closed__1;
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_MacroM_monadQuotation___closed__1;
lean_object* l_Lean_Syntax_getKind___closed__3;
lean_object* l_Lean_ParserDescr_sepBy___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScopeExt(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_addMacroScopes___spec__1(lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_mkStxLit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_toNat(lean_object*);
lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Init_LeanInit_1__mkMacroScopeName___closed__2;
lean_object* l_Lean_ParserDescr_num(uint8_t);
lean_object* l_Lean_mkCIdentFrom___closed__2;
lean_object* l_Lean_Name_eraseMacroScopes___boxed(lean_object*);
lean_object* l_Lean_mkCTermIdFrom(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_strLitToAtom___boxed(lean_object*);
lean_object* l_Lean_Syntax_decodeStrLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtomFrom___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_symbol(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_9__decodeHexLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MacroM_monadQuotation___lambda__1(lean_object*, lean_object*);
uint8_t l_UInt32_decLe(uint32_t, uint32_t);
lean_object* l_Lean_ParserDescr_optional___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkAppStx___closed__2;
lean_object* l_Lean_ParserDescr_nonReservedSymbol(lean_object*, uint8_t);
lean_object* l_Lean_Name_hasMacroScopes___main___boxed(lean_object*);
lean_object* l_Lean_Name_hash___boxed(lean_object*);
lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lean_MacroM_monadQuotation___closed__2;
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_Syntax_decodeStrLitAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_11__decodeNatLitVal(lean_object*);
lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_mkAppStx___closed__1;
size_t lean_string_hash(lean_object*);
lean_object* l_Lean_ParserDescr_sepBy1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___boxed(lean_object*, lean_object*);
lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
lean_object* l_Lean_MacroM_monadQuotation___closed__4;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__3;
lean_object* _init_l_Lean_Name_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
size_t l_Lean_Name_hash(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
size_t x_2; 
x_2 = 1723;
return x_2;
}
else
{
size_t x_3; 
x_3 = lean_ctor_get_usize(x_1, 2);
return x_3;
}
}
}
lean_object* l_Lean_Name_hash___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Lean_Name_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Name_hashable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_hash___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Name_hashable() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Name_hashable___closed__1;
return x_1;
}
}
lean_object* lean_name_mk_string(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = l_Lean_Name_hash(x_1);
x_4 = lean_string_hash(x_2);
x_5 = lean_usize_mix_hash(x_3, x_4);
x_6 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_usize(x_6, 2, x_5);
return x_6;
}
}
lean_object* lean_name_mk_numeral(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = l_Lean_Name_hash(x_1);
x_4 = lean_usize_of_nat(x_2);
x_5 = lean_usize_mix_hash(x_3, x_4);
x_6 = lean_alloc_ctor(2, 2, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_usize(x_6, 2, x_5);
return x_6;
}
}
lean_object* l_Lean_mkNameSimple(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_name_mk_string(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Name_Name_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_name_eq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Name_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_Name_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Name_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Name_HasBeq___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Name_toStringWithSep___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[anonymous]");
return x_1;
}
}
lean_object* l_Lean_Name_toStringWithSep___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
x_3 = l_Lean_Name_toStringWithSep___main___closed__1;
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
if (lean_obj_tag(x_4) == 0)
{
return x_5;
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
x_7 = l_Lean_Name_toStringWithSep___main(x_1, x_4);
x_8 = lean_string_append(x_7, x_1);
x_9 = lean_string_append(x_8, x_5);
lean_dec(x_5);
return x_9;
}
}
default: 
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_20; 
x_20 = l_Nat_repr(x_13);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_box(0);
x_14 = x_21;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
x_15 = l_Lean_Name_toStringWithSep___main(x_1, x_12);
x_16 = lean_string_append(x_15, x_1);
x_17 = l_Nat_repr(x_13);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
return x_18;
}
}
}
}
}
lean_object* l_Lean_Name_toStringWithSep___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Name_toStringWithSep___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Name_toStringWithSep(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Name_toStringWithSep___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Name_toStringWithSep___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Name_toStringWithSep(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Name_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(".");
return x_1;
}
}
lean_object* l_Lean_Name_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Name_toString___closed__1;
x_3 = l_Lean_Name_toStringWithSep___main(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Name_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_toString), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Name_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Name_HasToString___closed__1;
return x_1;
}
}
lean_object* l_Lean_Name_append___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_inc(x_1);
return x_1;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Name_append___main(x_1, x_3);
x_6 = lean_name_mk_string(x_5, x_4);
return x_6;
}
default: 
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_Name_append___main(x_1, x_7);
x_10 = lean_name_mk_numeral(x_9, x_8);
return x_10;
}
}
}
}
lean_object* l_Lean_Name_append___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Name_append___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Name_append(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Name_append___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Name_append(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Name_HasAppend___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_append___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Name_HasAppend() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Name_HasAppend___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_NameGenerator_Inhabited___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_uniq");
return x_1;
}
}
lean_object* _init_l_Lean_NameGenerator_Inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_NameGenerator_Inhabited___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_NameGenerator_Inhabited___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameGenerator_Inhabited___closed__2;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_NameGenerator_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameGenerator_Inhabited___closed__3;
return x_1;
}
}
lean_object* l_Lean_NameGenerator_curr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_name_mk_numeral(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_NameGenerator_next(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Lean_NameGenerator_mkChild(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_name_mk_numeral(x_3, x_4);
x_6 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_5);
x_7 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_11);
lean_inc(x_10);
x_12 = lean_name_mk_numeral(x_10, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_nat_add(x_11, x_13);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
lean_object* l_Lean_ParserDescrCore_inhabited(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean_alloc_ctor(10, 2, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ParserDescrCore_inhabited___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParserDescrCore_inhabited(x_2);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_andthen(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_andthen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParserDescr_andthen(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_ParserDescr_orelse(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_orelse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParserDescr_orelse(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_ParserDescr_optional(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_optional___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_ParserDescr_optional(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_lookahead(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_lookahead___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_ParserDescr_lookahead(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_try(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(4, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_try___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_ParserDescr_try(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_many(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_many___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_ParserDescr_many(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_many1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_many1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_ParserDescr_many1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_sepBy(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(7, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_sepBy___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParserDescr_sepBy(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_ParserDescr_sepBy1(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(8, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_sepBy1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParserDescr_sepBy1(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_ParserDescr_node(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(9, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_node___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParserDescr_node(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_ParserDescr_symbol(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(10, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_symbol___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParserDescr_symbol(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_ParserDescr_num(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(12, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ParserDescr_num___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParserDescr_num(x_2);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_str(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(13, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ParserDescr_str___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParserDescr_str(x_2);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_char(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(14, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ParserDescr_char___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParserDescr_char(x_2);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_ident(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(15, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ParserDescr_ident___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParserDescr_ident(x_2);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_nonReservedSymbol(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(11, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_nonReservedSymbol___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_ParserDescr_nonReservedSymbol(x_1, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_ParserDescr_pushLeading() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(16);
return x_1;
}
}
lean_object* l_Lean_ParserDescr_parser(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(17, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ParserDescr_parser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParserDescr_parser(x_4, x_2, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Syntax_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_getKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("missing");
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_getKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Syntax_getKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Syntax_getKind___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ident");
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_getKind___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Syntax_getKind___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_getKind(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getKind___closed__2;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
return x_3;
}
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_name_mk_string(x_5, x_4);
return x_6;
}
default: 
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = l_Lean_Syntax_getKind___closed__4;
return x_7;
}
}
}
}
uint8_t l_Lean_Syntax_isOfKind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Syntax_getKind(x_1);
x_4 = lean_name_eq(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_isOfKind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_getArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Syntax_inhabited;
x_5 = lean_array_get(x_4, x_3, x_2);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_getArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_getArgs(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_empty___closed__1;
return x_3;
}
}
}
lean_object* l_Lean_Syntax_getArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
return x_2;
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
lean_object* _init_l___private_Init_LeanInit_1__mkMacroScopeName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_@");
return x_1;
}
}
lean_object* _init_l___private_Init_LeanInit_1__mkMacroScopeName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_hyg");
return x_1;
}
}
lean_object* l___private_Init_LeanInit_1__mkMacroScopeName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l___private_Init_LeanInit_1__mkMacroScopeName___closed__1;
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = l_Lean_Name_append___main(x_4, x_1);
lean_dec(x_4);
x_6 = l___private_Init_LeanInit_1__mkMacroScopeName___closed__2;
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_addMacroScopeExt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Init_LeanInit_1__mkMacroScopeName(x_1, x_2);
x_5 = lean_name_mk_numeral(x_4, x_3);
return x_5;
}
}
lean_object* l_Lean_addMacroScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_addMacroScopeExt(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_List_foldl___main___at_Lean_addMacroScopes___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_name_mk_numeral(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_Lean_addMacroScopes(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Init_LeanInit_1__mkMacroScopeName(x_1, x_2);
x_5 = l_List_foldl___main___at_Lean_addMacroScopes___spec__1(x_4, x_3);
return x_5;
}
}
}
uint8_t l_Lean_Name_hasMacroScopes___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l___private_Init_LeanInit_1__mkMacroScopeName___closed__2;
x_5 = lean_string_dec_eq(x_3, x_4);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
x_1 = x_6;
goto _start;
}
}
}
}
lean_object* l_Lean_Name_hasMacroScopes___main___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Name_hasMacroScopes___main(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Name_hasMacroScopes(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Name_hasMacroScopes___main(x_1);
return x_2;
}
}
lean_object* l_Lean_Name_hasMacroScopes___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Name_hasMacroScopes(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_ExtractMacroScopesResult_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_ExtractMacroScopesResult_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ExtractMacroScopesResult_inhabited___closed__1;
return x_1;
}
}
lean_object* l___private_Init_LeanInit_2__assembleExtractedName___main(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = l_Lean_Name_inhabited;
x_5 = l_unreachable_x21___rarg(x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_name_mk_string(x_2, x_7);
x_1 = x_6;
x_2 = x_8;
goto _start;
}
default: 
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_name_mk_numeral(x_2, x_11);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_LeanInit_2__assembleExtractedName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_LeanInit_2__assembleExtractedName___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_LeanInit_3__extractMainModule___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_4 = l_Lean_ExtractMacroScopesResult_inhabited;
x_5 = l_unreachable_x21___rarg(x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = l___private_Init_LeanInit_1__mkMacroScopeName___closed__1;
x_9 = lean_string_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_3);
x_2 = x_6;
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = l___private_Init_LeanInit_2__assembleExtractedName___main(x_3, x_12);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_1);
return x_14;
}
}
default: 
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
lean_object* l___private_Init_LeanInit_3__extractMainModule(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_3__extractMainModule___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_4__extractMacroScopesAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
lean_dec(x_2);
x_3 = l_Lean_ExtractMacroScopesResult_inhabited;
x_4 = l_unreachable_x21___rarg(x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_List_reverse___rarg(x_2);
x_7 = lean_box(0);
x_8 = l___private_Init_LeanInit_3__extractMainModule___main(x_6, x_5, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
x_1 = x_9;
x_2 = x_11;
goto _start;
}
}
}
}
lean_object* l___private_Init_LeanInit_4__extractMacroScopesAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_LeanInit_4__extractMacroScopesAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_extractMacroScopes(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Name_hasMacroScopes___main(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l___private_Init_LeanInit_4__extractMacroScopesAux___main(x_1, x_6);
return x_7;
}
}
}
lean_object* l___private_Init_LeanInit_5__eraseMacroScopesAux___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Name_inhabited;
x_3 = l_unreachable_x21___rarg(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l___private_Init_LeanInit_1__mkMacroScopeName___closed__1;
x_7 = lean_string_dec_eq(x_5, x_6);
if (x_7 == 0)
{
x_1 = x_4;
goto _start;
}
else
{
lean_inc(x_4);
return x_4;
}
}
default: 
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 0);
x_1 = x_9;
goto _start;
}
}
}
}
lean_object* l___private_Init_LeanInit_5__eraseMacroScopesAux___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_LeanInit_5__eraseMacroScopesAux___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_5__eraseMacroScopesAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_LeanInit_5__eraseMacroScopesAux___main(x_1);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_5__eraseMacroScopesAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_LeanInit_5__eraseMacroScopesAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Name_eraseMacroScopes(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Name_hasMacroScopes___main(x_1);
if (x_2 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; 
x_3 = l___private_Init_LeanInit_5__eraseMacroScopesAux___main(x_1);
return x_3;
}
}
}
lean_object* l_Lean_Name_eraseMacroScopes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Name_eraseMacroScopes(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Macro_mkFreshName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Name_append___main(x_1, x_4);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
x_9 = lean_name_mk_numeral(x_7, x_8);
x_10 = l_Lean_Name_append___main(x_5, x_9);
lean_dec(x_5);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_8, x_11);
lean_dec(x_8);
lean_ctor_set(x_3, 1, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
lean_inc(x_15);
lean_inc(x_14);
x_16 = lean_name_mk_numeral(x_14, x_15);
x_17 = l_Lean_Name_append___main(x_5, x_16);
lean_dec(x_5);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_15, x_18);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
lean_object* l_Lean_Macro_mkFreshName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Macro_mkFreshName(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_MacroM_monadQuotation___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_MacroM_monadQuotation___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_MacroM_monadQuotation___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_MacroM_monadQuotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MacroM_monadQuotation___lambda__1___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_MacroM_monadQuotation___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MacroM_monadQuotation___lambda__2___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_MacroM_monadQuotation___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MacroM_monadQuotation___lambda__3), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_MacroM_monadQuotation___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_MacroM_monadQuotation___closed__1;
x_2 = l_Lean_MacroM_monadQuotation___closed__2;
x_3 = l_Lean_MacroM_monadQuotation___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_MacroM_monadQuotation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MacroM_monadQuotation___closed__4;
return x_1;
}
}
lean_object* l_Lean_MacroM_monadQuotation___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MacroM_monadQuotation___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_MacroM_monadQuotation___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MacroM_monadQuotation___lambda__2(x_1, x_2);
lean_dec(x_1);
return x_3;
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
lean_object* l_Lean_mkIdentFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l_Lean_Syntax_getHeadInfo___main(x_1);
x_4 = l_Lean_Name_toString___closed__1;
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
lean_object* _init_l_Lean_mkCIdentFrom___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_root_");
return x_1;
}
}
lean_object* _init_l_Lean_mkCIdentFrom___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkCIdentFrom___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkCIdentFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = l_Lean_Syntax_getHeadInfo___main(x_1);
x_4 = l_Lean_Name_toString___closed__1;
lean_inc(x_2);
x_5 = l_Lean_Name_toStringWithSep___main(x_4, x_2);
x_6 = lean_string_utf8_byte_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_6);
x_9 = l_Lean_mkCIdentFrom___closed__2;
lean_inc(x_2);
x_10 = l_Lean_Name_append___main(x_9, x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_13);
return x_14;
}
}
lean_object* l_Lean_mkCIdentFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkCIdentFrom(x_1, x_2);
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
lean_object* l_Lean_Syntax_identToAtom(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_Lean_Name_eraseMacroScopes(x_3);
x_5 = l_Lean_Name_toString___closed__1;
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_4);
lean_inc(x_2);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
lean_object* l_Lean_Syntax_identToAtom___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_identToAtom(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* lean_mk_syntax_ident(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_box(0);
x_3 = l_Lean_Name_toString___closed__1;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_mkOptionalNode___closed__2() {
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
x_2 = l_Lean_mkOptionalNode___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_mkOptionalNode___closed__2;
x_5 = lean_array_push(x_4, x_3);
x_6 = l_Lean_nullKind;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
lean_object* _init_l_Lean_mkAppStx___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
lean_object* _init_l_Lean_mkAppStx___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkAppStx___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_mkAppStx___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
lean_object* _init_l_Lean_mkAppStx___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_mkAppStx___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_mkAppStx___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Term");
return x_1;
}
}
lean_object* _init_l_Lean_mkAppStx___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_mkAppStx___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_mkAppStx___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("app");
return x_1;
}
}
lean_object* _init_l_Lean_mkAppStx___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_mkAppStx___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_mkAppStx___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Lean_mkAppStx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_nullKind;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
x_5 = l_Lean_mkAppStx___closed__9;
x_6 = lean_array_push(x_5, x_1);
x_7 = lean_array_push(x_6, x_4);
x_8 = l_Lean_mkAppStx___closed__8;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
lean_object* _init_l_Lean_mkHole___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hole");
return x_1;
}
}
lean_object* _init_l_Lean_mkHole___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_mkHole___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_mkHole___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_");
return x_1;
}
}
lean_object* l_Lean_mkHole(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_mkHole___closed__3;
x_3 = l_Lean_mkAtomFrom(x_1, x_2);
x_4 = l_Lean_mkOptionalNode___closed__2;
x_5 = lean_array_push(x_4, x_3);
x_6 = l_Lean_mkHole___closed__2;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
lean_object* l_Lean_mkHole___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHole(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_mkTermIdFromIdent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("id");
return x_1;
}
}
lean_object* _init_l_Lean_mkTermIdFromIdent___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_mkTermIdFromIdent___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkTermIdFromIdent(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_mkAppStx___closed__9;
x_3 = lean_array_push(x_2, x_1);
x_4 = l_Lean_mkOptionalNode___closed__1;
x_5 = lean_array_push(x_3, x_4);
x_6 = l_Lean_mkTermIdFromIdent___closed__2;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = l_Lean_Syntax_inhabited;
x_9 = l_unreachable_x21___rarg(x_8);
return x_9;
}
}
}
lean_object* l_Lean_mkTermIdFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_mkIdentFrom(x_1, x_2);
x_4 = l_Lean_mkTermIdFromIdent(x_3);
return x_4;
}
}
lean_object* l_Lean_mkTermIdFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkTermIdFrom(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_mkCTermIdFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_mkCIdentFrom(x_1, x_2);
x_4 = l_Lean_mkTermIdFromIdent(x_3);
return x_4;
}
}
lean_object* l_Lean_mkCTermIdFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkCTermIdFrom(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_mkTermId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_mkTermIdFrom(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_mkCTermId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_mkCTermIdFrom(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_mkCAppStx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_Lean_mkCTermIdFrom(x_3, x_1);
x_5 = l_Lean_mkAppStx(x_4, x_2);
return x_5;
}
}
lean_object* l_Lean_mkStxLit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
x_5 = l_Lean_mkOptionalNode___closed__2;
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
lean_object* l___private_Init_LeanInit_6__decodeBinLitAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Init_LeanInit_6__decodeBinLitAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_6__decodeBinLitAux___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_6__decodeBinLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_6__decodeBinLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_6__decodeBinLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_6__decodeBinLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_7__decodeOctalLitAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Init_LeanInit_7__decodeOctalLitAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_7__decodeOctalLitAux___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_7__decodeOctalLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_7__decodeOctalLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_7__decodeOctalLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_7__decodeOctalLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_8__decodeHexDigit(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Init_LeanInit_8__decodeHexDigit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_LeanInit_8__decodeHexDigit(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_LeanInit_9__decodeHexLitAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l___private_Init_LeanInit_8__decodeHexDigit(x_1, x_2);
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
lean_object* l___private_Init_LeanInit_9__decodeHexLitAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_9__decodeHexLitAux___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_9__decodeHexLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_9__decodeHexLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_9__decodeHexLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_9__decodeHexLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_10__decodeDecimalLitAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Init_LeanInit_10__decodeDecimalLitAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_10__decodeDecimalLitAux___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_10__decodeDecimalLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_10__decodeDecimalLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_10__decodeDecimalLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_10__decodeDecimalLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___private_Init_LeanInit_11__decodeNatLitVal___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_11__decodeNatLitVal(lean_object* x_1) {
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
x_10 = l___private_Init_LeanInit_10__decodeDecimalLitAux___main(x_1, x_3, x_3);
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
x_28 = l___private_Init_LeanInit_10__decodeDecimalLitAux___main(x_1, x_3, x_3);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_unsigned_to_nat(2u);
x_30 = l___private_Init_LeanInit_7__decodeOctalLitAux___main(x_1, x_29, x_3);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_unsigned_to_nat(2u);
x_32 = l___private_Init_LeanInit_7__decodeOctalLitAux___main(x_1, x_31, x_3);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_unsigned_to_nat(2u);
x_34 = l___private_Init_LeanInit_6__decodeBinLitAux___main(x_1, x_33, x_3);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_unsigned_to_nat(2u);
x_36 = l___private_Init_LeanInit_6__decodeBinLitAux___main(x_1, x_35, x_3);
return x_36;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_unsigned_to_nat(2u);
x_42 = l___private_Init_LeanInit_9__decodeHexLitAux___main(x_1, x_41, x_3);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_unsigned_to_nat(2u);
x_44 = l___private_Init_LeanInit_9__decodeHexLitAux___main(x_1, x_43, x_3);
return x_44;
}
}
else
{
lean_object* x_45; 
x_45 = l___private_Init_LeanInit_11__decodeNatLitVal___closed__1;
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
lean_object* l___private_Init_LeanInit_11__decodeNatLitVal___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_LeanInit_11__decodeNatLitVal(x_1);
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
x_15 = l___private_Init_LeanInit_11__decodeNatLitVal(x_14);
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
lean_object* _init_l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 9;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__3() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 39;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__4() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 34;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__5() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 92;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_12__decodeQuotedChar(lean_object* x_1, lean_object* x_2) {
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
x_20 = l___private_Init_LeanInit_8__decodeHexDigit(x_1, x_4);
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
x_25 = l___private_Init_LeanInit_8__decodeHexDigit(x_1, x_24);
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
x_30 = l___private_Init_LeanInit_8__decodeHexDigit(x_1, x_29);
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
x_35 = l___private_Init_LeanInit_8__decodeHexDigit(x_1, x_34);
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
x_77 = l___private_Init_LeanInit_8__decodeHexDigit(x_1, x_4);
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
x_82 = l___private_Init_LeanInit_8__decodeHexDigit(x_1, x_81);
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
x_112 = l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__1;
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
x_115 = l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__2;
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
x_118 = l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__3;
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
x_121 = l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__4;
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
x_124 = l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__5;
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_4);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
lean_object* l___private_Init_LeanInit_12__decodeQuotedChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_LeanInit_12__decodeQuotedChar(x_1, x_2);
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
x_12 = l___private_Init_LeanInit_12__decodeQuotedChar(x_1, x_5);
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
x_9 = l___private_Init_LeanInit_12__decodeQuotedChar(x_1, x_8);
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
lean_object* l_Lean_Syntax_identToStrLit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_toString___closed__1;
x_5 = l_Lean_Name_toStringWithSep___main(x_4, x_3);
x_6 = l_Lean_mkStxStrLit(x_5, x_2);
return x_6;
}
else
{
return x_1;
}
}
}
lean_object* l_Lean_Syntax_strLitToAtom(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isStrLit_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Syntax_getHeadInfo___main(x_1);
x_5 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
}
lean_object* l_Lean_Syntax_strLitToAtom___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_strLitToAtom(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Syntax_termIdToAntiquot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("antiquot");
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_termIdToAntiquot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_Syntax_termIdToAntiquot___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Syntax_termIdToAntiquot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("$");
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_termIdToAntiquot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_termIdToAntiquot(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_3 = l_Lean_Syntax_termIdToAntiquot___closed__3;
x_4 = l_Lean_mkAtomFrom(x_1, x_3);
x_5 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_6 = l_Lean_mkAtomFrom(x_1, x_5);
x_7 = l_Lean_mkAtomFrom(x_1, x_2);
x_8 = l_Lean_Syntax_termIdToAntiquot___closed__4;
x_9 = lean_array_push(x_8, x_4);
x_10 = lean_array_push(x_9, x_1);
x_11 = lean_array_push(x_10, x_6);
x_12 = lean_array_push(x_11, x_7);
x_13 = l_Lean_mkOptionalNode___closed__1;
x_14 = lean_array_push(x_12, x_13);
x_15 = l_Lean_Syntax_termIdToAntiquot___closed__2;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
lean_object* l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_array_push(x_4, x_7);
x_9 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_9;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_getSepElems___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_empty___closed__1;
x_5 = l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1___rarg(x_2, x_1, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_getSepElems(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_getSepElems___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_getSepElems___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_getSepElems___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_String_Basic(lean_object*);
lean_object* initialize_Init_Data_Array_Basic(lean_object*);
lean_object* initialize_Init_Data_UInt(lean_object*);
lean_object* initialize_Init_Data_Hashable(lean_object*);
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Control_EState(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_LeanInit(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Hashable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_EState(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Name_inhabited = _init_l_Lean_Name_inhabited();
lean_mark_persistent(l_Lean_Name_inhabited);
l_Lean_Name_hashable___closed__1 = _init_l_Lean_Name_hashable___closed__1();
lean_mark_persistent(l_Lean_Name_hashable___closed__1);
l_Lean_Name_hashable = _init_l_Lean_Name_hashable();
lean_mark_persistent(l_Lean_Name_hashable);
l_Lean_Name_HasBeq___closed__1 = _init_l_Lean_Name_HasBeq___closed__1();
lean_mark_persistent(l_Lean_Name_HasBeq___closed__1);
l_Lean_Name_HasBeq = _init_l_Lean_Name_HasBeq();
lean_mark_persistent(l_Lean_Name_HasBeq);
l_Lean_Name_toStringWithSep___main___closed__1 = _init_l_Lean_Name_toStringWithSep___main___closed__1();
lean_mark_persistent(l_Lean_Name_toStringWithSep___main___closed__1);
l_Lean_Name_toString___closed__1 = _init_l_Lean_Name_toString___closed__1();
lean_mark_persistent(l_Lean_Name_toString___closed__1);
l_Lean_Name_HasToString___closed__1 = _init_l_Lean_Name_HasToString___closed__1();
lean_mark_persistent(l_Lean_Name_HasToString___closed__1);
l_Lean_Name_HasToString = _init_l_Lean_Name_HasToString();
lean_mark_persistent(l_Lean_Name_HasToString);
l_Lean_Name_HasAppend___closed__1 = _init_l_Lean_Name_HasAppend___closed__1();
lean_mark_persistent(l_Lean_Name_HasAppend___closed__1);
l_Lean_Name_HasAppend = _init_l_Lean_Name_HasAppend();
lean_mark_persistent(l_Lean_Name_HasAppend);
l_Lean_NameGenerator_Inhabited___closed__1 = _init_l_Lean_NameGenerator_Inhabited___closed__1();
lean_mark_persistent(l_Lean_NameGenerator_Inhabited___closed__1);
l_Lean_NameGenerator_Inhabited___closed__2 = _init_l_Lean_NameGenerator_Inhabited___closed__2();
lean_mark_persistent(l_Lean_NameGenerator_Inhabited___closed__2);
l_Lean_NameGenerator_Inhabited___closed__3 = _init_l_Lean_NameGenerator_Inhabited___closed__3();
lean_mark_persistent(l_Lean_NameGenerator_Inhabited___closed__3);
l_Lean_NameGenerator_Inhabited = _init_l_Lean_NameGenerator_Inhabited();
lean_mark_persistent(l_Lean_NameGenerator_Inhabited);
l_Lean_ParserDescr_pushLeading = _init_l_Lean_ParserDescr_pushLeading();
lean_mark_persistent(l_Lean_ParserDescr_pushLeading);
l_Lean_Syntax_inhabited = _init_l_Lean_Syntax_inhabited();
lean_mark_persistent(l_Lean_Syntax_inhabited);
l_Lean_Syntax_getKind___closed__1 = _init_l_Lean_Syntax_getKind___closed__1();
lean_mark_persistent(l_Lean_Syntax_getKind___closed__1);
l_Lean_Syntax_getKind___closed__2 = _init_l_Lean_Syntax_getKind___closed__2();
lean_mark_persistent(l_Lean_Syntax_getKind___closed__2);
l_Lean_Syntax_getKind___closed__3 = _init_l_Lean_Syntax_getKind___closed__3();
lean_mark_persistent(l_Lean_Syntax_getKind___closed__3);
l_Lean_Syntax_getKind___closed__4 = _init_l_Lean_Syntax_getKind___closed__4();
lean_mark_persistent(l_Lean_Syntax_getKind___closed__4);
l___private_Init_LeanInit_1__mkMacroScopeName___closed__1 = _init_l___private_Init_LeanInit_1__mkMacroScopeName___closed__1();
lean_mark_persistent(l___private_Init_LeanInit_1__mkMacroScopeName___closed__1);
l___private_Init_LeanInit_1__mkMacroScopeName___closed__2 = _init_l___private_Init_LeanInit_1__mkMacroScopeName___closed__2();
lean_mark_persistent(l___private_Init_LeanInit_1__mkMacroScopeName___closed__2);
l_Lean_ExtractMacroScopesResult_inhabited___closed__1 = _init_l_Lean_ExtractMacroScopesResult_inhabited___closed__1();
lean_mark_persistent(l_Lean_ExtractMacroScopesResult_inhabited___closed__1);
l_Lean_ExtractMacroScopesResult_inhabited = _init_l_Lean_ExtractMacroScopesResult_inhabited();
lean_mark_persistent(l_Lean_ExtractMacroScopesResult_inhabited);
l_Lean_MacroM_monadQuotation___closed__1 = _init_l_Lean_MacroM_monadQuotation___closed__1();
lean_mark_persistent(l_Lean_MacroM_monadQuotation___closed__1);
l_Lean_MacroM_monadQuotation___closed__2 = _init_l_Lean_MacroM_monadQuotation___closed__2();
lean_mark_persistent(l_Lean_MacroM_monadQuotation___closed__2);
l_Lean_MacroM_monadQuotation___closed__3 = _init_l_Lean_MacroM_monadQuotation___closed__3();
lean_mark_persistent(l_Lean_MacroM_monadQuotation___closed__3);
l_Lean_MacroM_monadQuotation___closed__4 = _init_l_Lean_MacroM_monadQuotation___closed__4();
lean_mark_persistent(l_Lean_MacroM_monadQuotation___closed__4);
l_Lean_MacroM_monadQuotation = _init_l_Lean_MacroM_monadQuotation();
lean_mark_persistent(l_Lean_MacroM_monadQuotation);
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
l_Lean_mkCIdentFrom___closed__1 = _init_l_Lean_mkCIdentFrom___closed__1();
lean_mark_persistent(l_Lean_mkCIdentFrom___closed__1);
l_Lean_mkCIdentFrom___closed__2 = _init_l_Lean_mkCIdentFrom___closed__2();
lean_mark_persistent(l_Lean_mkCIdentFrom___closed__2);
l_Lean_mkOptionalNode___closed__1 = _init_l_Lean_mkOptionalNode___closed__1();
lean_mark_persistent(l_Lean_mkOptionalNode___closed__1);
l_Lean_mkOptionalNode___closed__2 = _init_l_Lean_mkOptionalNode___closed__2();
lean_mark_persistent(l_Lean_mkOptionalNode___closed__2);
l_Lean_mkAppStx___closed__1 = _init_l_Lean_mkAppStx___closed__1();
lean_mark_persistent(l_Lean_mkAppStx___closed__1);
l_Lean_mkAppStx___closed__2 = _init_l_Lean_mkAppStx___closed__2();
lean_mark_persistent(l_Lean_mkAppStx___closed__2);
l_Lean_mkAppStx___closed__3 = _init_l_Lean_mkAppStx___closed__3();
lean_mark_persistent(l_Lean_mkAppStx___closed__3);
l_Lean_mkAppStx___closed__4 = _init_l_Lean_mkAppStx___closed__4();
lean_mark_persistent(l_Lean_mkAppStx___closed__4);
l_Lean_mkAppStx___closed__5 = _init_l_Lean_mkAppStx___closed__5();
lean_mark_persistent(l_Lean_mkAppStx___closed__5);
l_Lean_mkAppStx___closed__6 = _init_l_Lean_mkAppStx___closed__6();
lean_mark_persistent(l_Lean_mkAppStx___closed__6);
l_Lean_mkAppStx___closed__7 = _init_l_Lean_mkAppStx___closed__7();
lean_mark_persistent(l_Lean_mkAppStx___closed__7);
l_Lean_mkAppStx___closed__8 = _init_l_Lean_mkAppStx___closed__8();
lean_mark_persistent(l_Lean_mkAppStx___closed__8);
l_Lean_mkAppStx___closed__9 = _init_l_Lean_mkAppStx___closed__9();
lean_mark_persistent(l_Lean_mkAppStx___closed__9);
l_Lean_mkHole___closed__1 = _init_l_Lean_mkHole___closed__1();
lean_mark_persistent(l_Lean_mkHole___closed__1);
l_Lean_mkHole___closed__2 = _init_l_Lean_mkHole___closed__2();
lean_mark_persistent(l_Lean_mkHole___closed__2);
l_Lean_mkHole___closed__3 = _init_l_Lean_mkHole___closed__3();
lean_mark_persistent(l_Lean_mkHole___closed__3);
l_Lean_mkTermIdFromIdent___closed__1 = _init_l_Lean_mkTermIdFromIdent___closed__1();
lean_mark_persistent(l_Lean_mkTermIdFromIdent___closed__1);
l_Lean_mkTermIdFromIdent___closed__2 = _init_l_Lean_mkTermIdFromIdent___closed__2();
lean_mark_persistent(l_Lean_mkTermIdFromIdent___closed__2);
l___private_Init_LeanInit_11__decodeNatLitVal___closed__1 = _init_l___private_Init_LeanInit_11__decodeNatLitVal___closed__1();
lean_mark_persistent(l___private_Init_LeanInit_11__decodeNatLitVal___closed__1);
l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__1 = _init_l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__1();
lean_mark_persistent(l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__1);
l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__2 = _init_l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__2();
lean_mark_persistent(l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__2);
l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__3 = _init_l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__3();
lean_mark_persistent(l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__3);
l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__4 = _init_l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__4();
lean_mark_persistent(l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__4);
l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__5 = _init_l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__5();
lean_mark_persistent(l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__5);
l_Lean_Syntax_termIdToAntiquot___closed__1 = _init_l_Lean_Syntax_termIdToAntiquot___closed__1();
lean_mark_persistent(l_Lean_Syntax_termIdToAntiquot___closed__1);
l_Lean_Syntax_termIdToAntiquot___closed__2 = _init_l_Lean_Syntax_termIdToAntiquot___closed__2();
lean_mark_persistent(l_Lean_Syntax_termIdToAntiquot___closed__2);
l_Lean_Syntax_termIdToAntiquot___closed__3 = _init_l_Lean_Syntax_termIdToAntiquot___closed__3();
lean_mark_persistent(l_Lean_Syntax_termIdToAntiquot___closed__3);
l_Lean_Syntax_termIdToAntiquot___closed__4 = _init_l_Lean_Syntax_termIdToAntiquot___closed__4();
lean_mark_persistent(l_Lean_Syntax_termIdToAntiquot___closed__4);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
