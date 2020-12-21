// Lean compiler output
// Module: Init.Meta
// Imports: Init.Data.Array.Basic
#include <lean/lean.h>
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
lean_object* l_Array_getSepElems___rarg___boxed(lean_object*);
lean_object* l_Lean_Syntax_setHeadInfoAux_match__2(lean_object*);
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_identToAtom_match__1(lean_object*);
lean_object* l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_decodeNameLitAux___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Syntax_isIdOrAtom_x3f___boxed(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__6___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setInfo_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_setTailInfoAux(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteName___closed__5;
lean_object* l_Lean_Syntax_isNameLit_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateFirst___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_strLitToAtom___closed__3;
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instQuoteBool(uint8_t);
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_instReprOption___rarg___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_evalOptPrio_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStr___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateFirst___at_Lean_Syntax_setHeadInfoAux___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object*);
lean_object* l___private_Init_Meta_0__Array_filterSepElemsMAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeHexDigit(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateFirst_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__2___rarg(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint32_t l_Lean_idBeginEscape;
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrQuotedChar_match__1(lean_object*);
extern lean_object* l_Lean_Parser_Syntax_addPrio___closed__4;
lean_object* l_Array_mapMUnsafe_map___at_Lean_expandMacros___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Syntax_getTailInfo___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeStrLitAux_match__1(lean_object*);
lean_object* l_Lean_Syntax_mkSep(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateFirst_match__1(lean_object*, lean_object*);
lean_object* l_Array_filterSepElemsM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instQuoteSubstring___closed__3;
lean_object* l_Lean_Name_capitalize(lean_object*);
lean_object* l_Lean_Syntax_isAtom___boxed(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateFirst(lean_object*);
lean_object* l_Lean_monadNameGeneratorLift(lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instQuoteBool_match__1___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_hasArgs_match__1(lean_object*);
lean_object* l_Lean_mkSepArray_match__2___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteName___closed__7;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11811____closed__18;
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_toNat___boxed(lean_object*);
lean_object* l_Lean_Syntax_identToAtom_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2___closed__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__3(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__5;
lean_object* l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_decodeNameLitAux___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeOctalLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__3;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_findAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Char_isDigit(uint32_t);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_Lean_Syntax_setTailInfo_match__1(lean_object*);
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_isGreek___boxed(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeBinLitAux(lean_object*, lean_object*, lean_object*);
uint32_t l_Lean_idEndEscape;
lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
extern lean_object* l_instReprBool___closed__1;
lean_object* l_Lean_isIdRest___boxed(lean_object*);
lean_object* l_Lean_instQuoteProd(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
uint8_t l_Lean_isIdBeginEscape(uint32_t);
lean_object* l_Lean_Syntax_isLit_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkScientificLit(lean_object*, lean_object*);
lean_object* l_Lean_isIdFirst___boxed(lean_object*);
lean_object* l_Lean_mkHole___boxed(lean_object*);
lean_object* l___private_Init_Meta_0__Array_filterSepElemsMAux___at_Array_filterSepElems___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfoAux_match__2(lean_object*);
lean_object* l_Lean_Syntax_setInfo_match__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkApp_match__1(lean_object*);
extern lean_object* l_Array_getEvenElems___rarg___closed__1;
lean_object* l_Lean_Syntax_strLitToAtom_match__1(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeHexDigit___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
lean_object* l_Lean_instQuoteArray(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instQuoteProd_match__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Applicative_seqRight___default___rarg___closed__1;
lean_object* l_Lean_Syntax_identToStrLit(lean_object*);
lean_object* l_Array_filterSepElemsM___at_Array_filterSepElems___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Init_Notation___hyg_13581____closed__7;
lean_object* l_Lean_instQuoteList___rarg(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_NameGenerator_namePrefix___default;
lean_object* l_Lean_Syntax_expandInterpolatedStr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterSepElems___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
lean_object* l_Lean_instQuoteBool___closed__1;
uint8_t l_USize_decLt(size_t, size_t);
extern lean_object* l_Lean_nameLitKind;
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrLit_loop_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_isNatLitAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instQuoteBool___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkSep___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
lean_object* l_Lean_isSubScriptAlnum___boxed(lean_object*);
lean_object* l_Array_mapSepElems(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteName___closed__4;
lean_object* l_Lean_Name_instReprName(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Name_capitalize_match__1(lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instQuoteSubstring___closed__1;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isAtom_match__1(lean_object*);
lean_object* l_Lean_instQuoteSubstring___closed__2;
lean_object* l_Lean_Syntax_strLitToAtom(lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteName___closed__8;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_9172____closed__7;
lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrLit_loop___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_getElems___rarg(lean_object*);
lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
lean_object* l_Array_mapSepElems___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__6;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalPrio___closed__1;
lean_object* l_Lean_instQuoteBool___closed__5;
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
lean_object* l_Lean_instQuoteList(lean_object*);
lean_object* l_Lean_Syntax_isIdOrAtom_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_isIdent_match__1(lean_object*);
lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__4___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Name_appendAfter_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setHeadInfoAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
lean_object* l_Lean_Syntax_mkStrLit___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkApp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instQuoteString(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeDecimalLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeStrLitAux_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteName___closed__6;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_termEvalPrio_x21_____closed__3;
lean_object* l_Lean_instQuoteProd___rarg___closed__2;
lean_object* l_Lean_Syntax_setHeadInfoAux_match__1(lean_object*);
lean_object* l_Lean_mkFreshId___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_identToStrLit_match__1(lean_object*);
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux(lean_object*);
lean_object* l_Lean_Syntax_mkCApp(lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind;
lean_object* l_Lean_Syntax_decodeCharLit_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__3(lean_object*);
lean_object* l_Lean_Syntax_isCharLit_x3f_match__1(lean_object*);
lean_object* l_Array_getSepElems(lean_object*);
lean_object* l_Lean_monadNameGeneratorLift___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_getElems(lean_object*);
lean_object* l_Lean_Syntax_getId___boxed(lean_object*);
lean_object* l_Lean_Syntax_hasArgs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_termEvalPrio_x21_____closed__5;
lean_object* l___private_Init_Meta_0__Lean_quoteList___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object*);
lean_object* l_Lean_termEvalPrec_x21_____closed__7;
lean_object* l_Lean_Syntax_setTailInfo_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateLast_match__1(lean_object*, lean_object*);
lean_object* l_Lean_instQuoteProd___rarg___closed__1;
lean_object* l_Lean_Syntax_isStrLit_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_capitalize_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_copyInfo(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeHexLitAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isNumericSubscript(uint32_t);
lean_object* l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_decodeNameLitAux___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__1(lean_object*);
lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*);
lean_object* l_Lean_expandMacros_match__1(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteOption___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteName___closed__9;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instQuoteBool___closed__6;
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__14;
lean_object* l_Lean_mkFreshId___rarg(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11259____closed__9;
lean_object* l_String_capitalize(lean_object*);
lean_object* l_Lean_evalOptPrec_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameGenerator_next(lean_object*);
lean_object* l_Lean_Syntax_setHeadInfo_match__1(lean_object*);
lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object*);
lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object*);
lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object*);
extern lean_object* l_instReprBool___closed__3;
lean_object* l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_decodeNameLitAux___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_appendAfter_match__1(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Syntax_replaceInfo___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__2;
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l_Array_getSepElems___rarg(lean_object*);
extern lean_object* l_Lean_reservedMacroScope;
lean_object* l_Lean_Syntax_copyInfo___boxed(lean_object*, lean_object*);
lean_object* l_Lean_NameGenerator_namePrefix___default___closed__1;
lean_object* l_Lean_mkNullNode(lean_object*);
lean_object* l_Lean_Name_instToStringName;
extern lean_object* l_Lean_Parser_Syntax_addPrio___closed__2;
lean_object* l_Lean_instQuoteBool___closed__3;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Array_mapSepElemsM___at_Array_mapSepElems___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Syntax_getTailInfo___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instQuoteSubstring___boxed(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrQuotedChar_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instQuoteSubstring(lean_object*);
extern lean_object* l_Lean_instInhabitedSourceInfo___closed__1;
lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f_match__1(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_strLitToAtom_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_charLitKind;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12721____closed__11;
lean_object* l_Lean_NameGenerator_idx___default;
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId(lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalOptPrec_match__1(lean_object*);
lean_object* l_Lean_termEvalPrio_x21_____closed__7;
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Lean_mkOptionalNode_match__1(lean_object*);
lean_object* l_Lean_Syntax_replaceInfo(lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind___closed__2;
lean_object* l___private_Init_Meta_0__Lean_quoteName___closed__2;
lean_object* l_Lean_Syntax_isNameLit_x3f_match__1(lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__2(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteName(lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo_match__1(lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f_match__1(lean_object*);
lean_object* l___private_Init_Meta_0__Array_filterSepElemsMAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Syntax_findAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfoAux_match__1(lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_Nat_pred(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Array_filterSepElemsMAux(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12721____closed__8;
lean_object* l_Lean_Name_appendIndexAfter_match__1(lean_object*);
lean_object* l_Lean_termEvalPrec_x21_____closed__3;
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeNameLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_copyTailInfo_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalOptPrec(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__4;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNone_match__1(lean_object*);
lean_object* l_Array_filterSepElemsM(lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* l_Lean_Syntax_copyTailInfo___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_appendBefore_match__1(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeNameLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isNumericSubscript___boxed(lean_object*);
lean_object* l_Lean_evalOptPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptionalIdent_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_termEvalPrec_x21_____closed__5;
lean_object* l_Lean_NameGenerator_mkChild(lean_object*);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__10;
lean_object* l_Lean_mkSepArray_match__2(lean_object*);
lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11259____closed__8;
lean_object* l_Lean_Syntax_getId_match__1___rarg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrLit(lean_object*);
extern lean_object* l_term___x2b_x2b_____closed__2;
lean_object* l_Lean_Syntax_getOptionalIdent_x3f_match__1(lean_object*);
lean_object* l_Lean_Syntax_decodeStrLit___boxed(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteName___closed__1;
lean_object* l_Lean_Name_appendIndexAfter_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Array_mapSepElems___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameGenerator_namePrefix___default___closed__2;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isIdEndEscape(uint32_t);
lean_object* l_Lean_Syntax_unsetTrailing_match__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateLast___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_decodeCharLit(lean_object*);
lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___closed__1;
lean_object* l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__1;
uint8_t l_Char_isAlpha(uint32_t);
lean_object* l_Lean_Option_hasQuote(lean_object*);
uint8_t l_Lean_Syntax_isAtom(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Array_getSepElems___spec__1(lean_object*);
lean_object* l_Lean_Syntax_isToken_match__1(lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
uint8_t l_Lean_isLetterLike(uint32_t);
lean_object* l_Lean_Syntax_SepArray_instCoeSepArrayArraySyntax(lean_object*);
lean_object* l_Lean_evalPrec(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_toNat_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedNameGenerator___closed__1;
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_Lean_isLetterLike___boxed(lean_object*);
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object*);
lean_object* l_Lean_Syntax_isAtom_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isIdOrAtom_x3f_match__1(lean_object*);
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Array_mapSepElems___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_expandMacros___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instQuoteProd_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfoAux_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f_match__2(lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkApp___closed__1;
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_Name_instReprName___closed__1;
lean_object* l_Lean_termEvalPrec_x21_____closed__6;
lean_object* l_Lean_Name_instReprName___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__6(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteName_match__1(lean_object*);
lean_object* l_Lean_Name_appendAfter(lean_object*, lean_object*);
lean_object* l_Lean_termEvalPrio_x21_____closed__1;
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l_Lean_termEvalPrio_x21_____closed__2;
lean_object* l_Lean_Syntax_isIdent_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHole(lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStr___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_scientificLitKind;
lean_object* l_Array_foldlMUnsafe_fold___at_Array_getSepElems___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instQuoteString___boxed(lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks___closed__1;
lean_object* l_Lean_instQuoteBool___closed__2;
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__3___rarg(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2094____closed__4;
extern lean_object* l_Lean_Parser_Syntax_subPrio___closed__2;
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_hasArgs(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteList(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_isNatLitAux_match__1(lean_object*);
lean_object* l_String_quote(lean_object*);
uint8_t l_Char_isAlphanum(uint32_t);
lean_object* l_Lean_instInhabitedNameGenerator;
lean_object* l_Lean_Syntax_isScientificLit_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object*);
uint8_t l_Lean_isGreek(uint32_t);
lean_object* l___private_Init_Meta_0__Lean_quoteList_match__1(lean_object*, lean_object*);
lean_object* l_Lean_termEvalPrio_x21__;
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
lean_object* l_Lean_termEvalPrec_x21__;
lean_object* l_Array_filterSepElems(lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM___at_Array_mapSepElems___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_identToAtom(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeHexLitAux_match__1(lean_object*);
lean_object* l_Lean_Name_appendBefore_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSepArray_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_instQuoteSubstring___closed__4;
lean_object* l_Lean_mkOptionalNode_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSepArray_match__1(lean_object*);
lean_object* l_Lean_Syntax_setHeadInfo_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_expandMacros___boxed__const__1;
lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object*);
lean_object* l_Lean_evalPrec___closed__1;
lean_object* l_Lean_Syntax_decodeCharLit_match__1(lean_object*);
lean_object* l_Lean_Syntax_replaceInfo_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___closed__1;
lean_object* l_Lean_NameGenerator_curr(lean_object*);
lean_object* l_Lean_Syntax_SepArray_getElems___rarg___boxed(lean_object*);
lean_object* l_Lean_Syntax_getId_match__1(lean_object*);
lean_object* l_Lean_Syntax_isToken_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_isCharLit_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_termEvalPrio_x21_____closed__6;
lean_object* l_Lean_isIdBeginEscape___boxed(lean_object*);
lean_object* l___private_Init_Meta_0__Array_filterSepElemsMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStr___lambda__1___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeHexLitAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
lean_object* l_Lean_Syntax_copyInfo_match__1(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_isNatLitAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteName_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__2(lean_object*);
lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteOption(lean_object*);
lean_object* l_Lean_expandMacros_match__2(lean_object*);
lean_object* l_Lean_instQuoteNat(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_expandMacros(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateLast(lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f_match__1(lean_object*);
lean_object* l_Lean_Syntax_decodeNameLit(lean_object*);
lean_object* l_Lean_Name_toStringWithSep_match__1(lean_object*);
lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object*);
lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object*);
lean_object* l_Lean_Macro_expandMacro_x3fImp(lean_object*, lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object*, lean_object*);
lean_object* l_Lean_isIdEndEscape___boxed(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_Array_Basic___hyg_3426____closed__5;
lean_object* l_Lean_instQuoteBool___closed__4;
lean_object* l_Lean_termEvalPrec_x21_____closed__2;
lean_object* l_Lean_Syntax_unsetTrailing_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeStrLit(lean_object*);
uint8_t l_Lean_isIdFirst(uint32_t);
lean_object* l_Lean_instQuoteName;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_findAux_match__1(lean_object*);
lean_object* l_Lean_Syntax_isNone___boxed(lean_object*);
lean_object* l_Lean_instQuoteBool_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStr___lambda__1___closed__2;
lean_object* l_Lean_Syntax_isToken___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdentFrom___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkCIdentFrom___closed__1;
lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
lean_object* l_Lean_Syntax_identToStrLit_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_decodeNameLit___boxed(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_expandMacros_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_findAux___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_replaceInfo_match__1(lean_object*);
lean_object* l_Lean_Syntax_strLitToAtom___closed__2;
lean_object* l_Lean_Name_instReprName___closed__2;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_730____closed__8;
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
lean_object* l_Lean_Syntax_toNat_match__1(lean_object*);
lean_object* l_Lean_Syntax_setTailInfoAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateFirst___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_toNat(lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Name_appendBefore(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_strLitToAtom_match__2(lean_object*);
lean_object* l_Lean_mkOptionalNode___closed__2;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2351____closed__4;
lean_object* l_Lean_Syntax_getOptional_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_setHeadInfoAux_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__1(lean_object*);
lean_object* l_Lean_mkCIdentFrom___closed__2;
lean_object* l_Lean_instQuoteArray___rarg(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteName___closed__3;
lean_object* l_Lean_Syntax_SepArray_instCoeSepArrayArraySyntax___closed__1;
lean_object* l___private_Init_Meta_0__Array_filterSepElemsMAux___at_Array_filterSepElems___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_instCoeSepArrayArraySyntax___boxed(lean_object*);
lean_object* l_Lean_instQuoteProd___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isScientificLit_x3f_match__1(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteOption_match__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instCoeArraySyntaxSepArray(lean_object*);
lean_object* l_Lean_Syntax_strLitToAtom___boxed(lean_object*);
lean_object* l_Lean_Syntax_find_x3f(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeStrLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteList_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterSepElemsM___at_Array_filterSepElems___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteOption_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_monadNameGeneratorLift___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_myMacro____x40_Init_Meta___hyg_4040_(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_myMacro____x40_Init_Meta___hyg_4159_(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_myMacro____x40_Init_Meta___hyg_4388_(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_myMacro____x40_Init_Meta___hyg_4290_(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_myMacro____x40_Init_Meta___hyg_4507_(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_myMacro____x40_Init_Meta___hyg_3942_(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStr___closed__1;
lean_object* l_Lean_Syntax_decodeQuotedChar_match__5(lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSepArray___closed__1;
extern lean_object* l_Lean_Parser_Syntax_subPrec___closed__2;
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_UInt32_decLe(uint32_t, uint32_t);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__4(lean_object*);
lean_object* l_Lean_mkSepArray___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNone_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_copyTailInfo_match__1(lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__5___rarg(lean_object*, lean_object*);
lean_object* l_Lean_instQuoteName___closed__1;
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateLast_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Array_getSepElems___spec__1___rarg(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_strLitToAtom___closed__1;
lean_object* l_Lean_Syntax_findAux(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_copyInfo_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_termEvalPrec_x21_____closed__1;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lean_instQuoteSyntax;
lean_object* l_Lean_mkNode(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_copyTailInfo(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_quoteList___rarg___closed__1;
lean_object* l_Lean_instQuoteBool_match__1(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___closed__1;
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrLit_loop_match__1(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_strLitToAtom___closed__4;
lean_object* l_Lean_Syntax_getOptional_x3f_match__1(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11811____closed__19;
uint8_t l_Lean_Syntax_isToken(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object*);
lean_object* l_Lean_Name_instToStringName___closed__1;
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrLit___boxed(lean_object*);
lean_object* l_Lean_evalPrio(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_findSomeM_x3f___rarg___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object*, lean_object*);
lean_object* l_Lean_Option_hasQuote___rarg(lean_object*);
extern lean_object* l_Lean_interpolatedStrLitKind;
lean_object* l_Lean_termEvalPrec_x21_____closed__4;
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__8;
lean_object* l_Lean_termEvalPrio_x21_____closed__4;
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateLast___at_Lean_Syntax_setTailInfoAux___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isIdRest(uint32_t);
lean_object* l_Lean_Syntax_isIdent___boxed(lean_object*);
lean_object* l_Lean_expandMacros_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
lean_object* l_Char_ofNat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Syntax_replaceInfo___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_strLitToAtom_match__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_evalOptPrio_match__1(lean_object*);
uint8_t l_Lean_isGreek(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 913;
x_3 = x_2 <= x_1;
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint32_t x_5; uint8_t x_6; 
x_5 = 989;
x_6 = x_1 <= x_5;
return x_6;
}
}
}
lean_object* l_Lean_isGreek___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isGreek(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_isLetterLike(uint32_t x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; lean_object* x_20; lean_object* x_29; lean_object* x_38; uint8_t x_55; 
x_2 = 945;
x_55 = x_2 <= x_1;
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_box(0);
x_38 = x_56;
goto block_54;
}
else
{
uint32_t x_57; uint8_t x_58; 
x_57 = 969;
x_58 = x_1 <= x_57;
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_box(0);
x_38 = x_59;
goto block_54;
}
else
{
uint32_t x_60; uint8_t x_61; uint8_t x_62; 
x_60 = 955;
x_61 = x_1 == x_60;
x_62 = l_instDecidableNot___rarg(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_box(0);
x_38 = x_63;
goto block_54;
}
else
{
uint8_t x_64; 
x_64 = 1;
return x_64;
}
}
}
block_19:
{
uint32_t x_4; uint8_t x_5; 
lean_dec(x_3);
x_4 = 8448;
x_5 = x_4 <= x_1;
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 119964;
x_7 = x_6 <= x_1;
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint32_t x_9; uint8_t x_10; 
x_9 = 120223;
x_10 = x_1 <= x_9;
return x_10;
}
}
else
{
uint32_t x_11; uint8_t x_12; 
x_11 = 8527;
x_12 = x_1 <= x_11;
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 119964;
x_14 = x_13 <= x_1;
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
else
{
uint32_t x_16; uint8_t x_17; 
x_16 = 120223;
x_17 = x_1 <= x_16;
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = 1;
return x_18;
}
}
}
block_28:
{
uint32_t x_21; uint8_t x_22; 
lean_dec(x_20);
x_21 = 7936;
x_22 = x_21 <= x_1;
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_box(0);
x_3 = x_23;
goto block_19;
}
else
{
uint32_t x_24; uint8_t x_25; 
x_24 = 8190;
x_25 = x_1 <= x_24;
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_box(0);
x_3 = x_26;
goto block_19;
}
else
{
uint8_t x_27; 
x_27 = 1;
return x_27;
}
}
}
block_37:
{
uint32_t x_30; uint8_t x_31; 
lean_dec(x_29);
x_30 = 970;
x_31 = x_30 <= x_1;
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_box(0);
x_20 = x_32;
goto block_28;
}
else
{
uint32_t x_33; uint8_t x_34; 
x_33 = 1019;
x_34 = x_1 <= x_33;
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_box(0);
x_20 = x_35;
goto block_28;
}
else
{
uint8_t x_36; 
x_36 = 1;
return x_36;
}
}
}
block_54:
{
uint32_t x_39; uint8_t x_40; 
lean_dec(x_38);
x_39 = 913;
x_40 = x_39 <= x_1;
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_box(0);
x_29 = x_41;
goto block_37;
}
else
{
uint32_t x_42; uint8_t x_43; 
x_42 = 937;
x_43 = x_1 <= x_42;
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_box(0);
x_29 = x_44;
goto block_37;
}
else
{
uint32_t x_45; uint8_t x_46; uint8_t x_47; 
x_45 = 928;
x_46 = x_1 == x_45;
x_47 = l_instDecidableNot___rarg(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_box(0);
x_29 = x_48;
goto block_37;
}
else
{
uint32_t x_49; uint8_t x_50; uint8_t x_51; 
x_49 = 931;
x_50 = x_1 == x_49;
x_51 = l_instDecidableNot___rarg(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_box(0);
x_29 = x_52;
goto block_37;
}
else
{
uint8_t x_53; 
x_53 = 1;
return x_53;
}
}
}
}
}
}
}
lean_object* l_Lean_isLetterLike___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isLetterLike(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_isNumericSubscript(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 8320;
x_3 = x_2 <= x_1;
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint32_t x_5; uint8_t x_6; 
x_5 = 8329;
x_6 = x_1 <= x_5;
return x_6;
}
}
}
lean_object* l_Lean_isNumericSubscript___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isNumericSubscript(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_isSubScriptAlnum(uint32_t x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_isNumericSubscript(x_1);
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 8336;
x_4 = x_3 <= x_1;
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 7522;
x_6 = x_5 <= x_1;
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint32_t x_8; uint8_t x_9; 
x_8 = 7530;
x_9 = x_1 <= x_8;
return x_9;
}
}
else
{
uint32_t x_10; uint8_t x_11; 
x_10 = 8348;
x_11 = x_1 <= x_10;
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 7522;
x_13 = x_12 <= x_1;
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
else
{
uint32_t x_15; uint8_t x_16; 
x_15 = 7530;
x_16 = x_1 <= x_15;
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
}
}
else
{
uint8_t x_18; 
x_18 = 1;
return x_18;
}
}
}
lean_object* l_Lean_isSubScriptAlnum___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isSubScriptAlnum(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_isIdFirst(uint32_t x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Char_isAlpha(x_1);
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 95;
x_4 = x_1 == x_3;
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_isLetterLike(x_1);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
lean_object* l_Lean_isIdFirst___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isIdFirst(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_isIdRest(uint32_t x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Char_isAlphanum(x_1);
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 95;
x_4 = x_1 == x_3;
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 39;
x_6 = x_1 == x_5;
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 33;
x_8 = x_1 == x_7;
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 63;
x_10 = x_1 == x_9;
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_isLetterLike(x_1);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_isSubScriptAlnum(x_1);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = 1;
return x_18;
}
}
}
lean_object* l_Lean_isIdRest___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isIdRest(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static uint32_t _init_l_Lean_idBeginEscape() {
_start:
{
uint32_t x_1; 
x_1 = 171;
return x_1;
}
}
static uint32_t _init_l_Lean_idEndEscape() {
_start:
{
uint32_t x_1; 
x_1 = 187;
return x_1;
}
}
uint8_t l_Lean_isIdBeginEscape(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = l_Lean_idBeginEscape;
x_3 = x_1 == x_2;
return x_3;
}
}
lean_object* l_Lean_isIdBeginEscape___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isIdBeginEscape(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_isIdEndEscape(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = l_Lean_idEndEscape;
x_3 = x_1 == x_2;
return x_3;
}
}
lean_object* l_Lean_isIdEndEscape___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isIdEndEscape(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Name_toStringWithSep_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_12 = lean_box_usize(x_11);
x_13 = lean_apply_2(x_3, x_10, x_12);
return x_13;
}
else
{
lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_16 = lean_box_usize(x_15);
x_17 = lean_apply_3(x_5, x_9, x_14, x_16);
return x_17;
}
}
default: 
{
lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_21 = lean_box_usize(x_20);
x_22 = lean_apply_2(x_4, x_19, x_21);
return x_22;
}
else
{
lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_25 = lean_box_usize(x_24);
x_26 = lean_apply_3(x_6, x_18, x_23, x_25);
return x_26;
}
}
}
}
}
lean_object* l_Lean_Name_toStringWithSep_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Name_toStringWithSep_match__1___rarg), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Name_toStringWithSep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[anonymous]");
return x_1;
}
}
lean_object* l_Lean_Name_toStringWithSep(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
x_3 = l_Lean_Name_toStringWithSep___closed__1;
return x_3;
}
case 1:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Name_toStringWithSep(x_1, x_4);
x_8 = lean_string_append(x_7, x_1);
x_9 = lean_string_append(x_8, x_6);
lean_dec(x_6);
return x_9;
}
}
default: 
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Nat_repr(x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Name_toStringWithSep(x_1, x_10);
x_15 = lean_string_append(x_14, x_1);
x_16 = l_Nat_repr(x_13);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
return x_17;
}
}
}
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
static lean_object* _init_l_Lean_Name_toString___closed__1() {
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
x_3 = l_Lean_Name_toStringWithSep(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Name_instToStringName___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Name_toString___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Name_toStringWithSep___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Name_instToStringName() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Name_instToStringName___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Name_instReprName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("`");
return x_1;
}
}
static lean_object* _init_l_Lean_Name_instReprName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Name_instReprName___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Name_instReprName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Name_toString___closed__1;
x_4 = l_Lean_Name_toStringWithSep(x_3, x_1);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_Name_instReprName___closed__2;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
lean_object* l_Lean_Name_instReprName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Name_instReprName(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Name_capitalize_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_7 = lean_box_usize(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Name_capitalize_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Name_capitalize_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Name_capitalize(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_String_capitalize(x_3);
x_5 = lean_name_mk_string(x_2, x_4);
return x_5;
}
else
{
return x_1;
}
}
}
lean_object* l_Lean_Name_appendAfter_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_8 = lean_box_usize(x_7);
x_9 = lean_apply_4(x_3, x_5, x_6, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_4, x_1, x_2);
return x_10;
}
}
}
lean_object* l_Lean_Name_appendAfter_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Name_appendAfter_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Name_appendAfter(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_string_append(x_4, x_2);
lean_dec(x_2);
x_6 = lean_name_mk_string(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_name_mk_string(x_1, x_2);
return x_7;
}
}
}
lean_object* l_Lean_Name_appendIndexAfter_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_8 = lean_box_usize(x_7);
x_9 = lean_apply_4(x_3, x_5, x_6, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_4, x_1, x_2);
return x_10;
}
}
}
lean_object* l_Lean_Name_appendIndexAfter_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Name_appendIndexAfter_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Name_appendIndexAfter(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_myMacro____x40_Init_Notation___hyg_11811____closed__19;
x_6 = lean_string_append(x_4, x_5);
x_7 = l_Nat_repr(x_2);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_name_mk_string(x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Nat_repr(x_2);
x_11 = l_myMacro____x40_Init_Notation___hyg_11811____closed__19;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = lean_name_mk_string(x_1, x_12);
return x_13;
}
}
}
lean_object* l_Lean_Name_appendBefore_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_2);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_10 = lean_box_usize(x_9);
x_11 = lean_apply_4(x_4, x_7, x_8, x_10, x_2);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_15 = lean_box_usize(x_14);
x_16 = lean_apply_4(x_5, x_12, x_13, x_15, x_2);
return x_16;
}
}
}
}
lean_object* l_Lean_Name_appendBefore_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Name_appendBefore_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Name_appendBefore(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_name_mk_string(x_3, x_2);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_string_append(x_2, x_6);
lean_dec(x_6);
x_8 = lean_name_mk_string(x_5, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_name_mk_string(x_9, x_2);
x_12 = lean_name_mk_numeral(x_11, x_10);
return x_12;
}
}
}
}
static lean_object* _init_l_Lean_NameGenerator_namePrefix___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_uniq");
return x_1;
}
}
static lean_object* _init_l_Lean_NameGenerator_namePrefix___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_NameGenerator_namePrefix___default___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_NameGenerator_namePrefix___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameGenerator_namePrefix___default___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_NameGenerator_idx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedNameGenerator___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedNameGenerator() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedNameGenerator___closed__1;
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
lean_object* l_Lean_mkFreshId___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
x_8 = lean_name_mk_numeral(x_6, x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_7, x_10);
lean_dec(x_7);
lean_ctor_set(x_4, 1, x_11);
x_12 = lean_apply_1(x_9, x_4);
x_13 = lean_alloc_closure((void*)(l_ReaderT_instMonadReaderT___rarg___lambda__4___boxed), 3, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_8);
x_14 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
lean_inc(x_16);
lean_inc(x_15);
x_17 = lean_name_mk_numeral(x_15, x_16);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_16, x_19);
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_apply_1(x_18, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instMonadReaderT___rarg___lambda__4___boxed), 3, 2);
lean_closure_set(x_23, 0, x_2);
lean_closure_set(x_23, 1, x_17);
x_24 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_22, x_23);
return x_24;
}
}
}
lean_object* l_Lean_mkFreshId___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_mkFreshId___rarg___lambda__1), 4, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
lean_closure_set(x_5, 2, x_3);
x_6 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_mkFreshId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkFreshId___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_monadNameGeneratorLift___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_3);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_monadNameGeneratorLift___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_monadNameGeneratorLift___rarg___lambda__1), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_Lean_monadNameGeneratorLift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_monadNameGeneratorLift___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_getTailInfo_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_apply_1(x_5, x_1);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_4, x_7, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_2(x_2, x_10, x_11);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_4(x_3, x_13, x_14, x_15, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Syntax_getTailInfo_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_getTailInfo_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Syntax_getTailInfo___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_8 = lean_array_fget(x_1, x_7);
x_9 = l_Lean_Syntax_getTailInfo(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
x_2 = x_7;
x_3 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_7);
return x_9;
}
}
else
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
}
}
}
lean_object* l_Lean_Syntax_getTailInfo(lean_object* x_1) {
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
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_Syntax_getTailInfo___spec__1(x_3, x_4, lean_box(0));
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Syntax_getTailInfo___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findSomeRevM_x3f_find___at_Lean_Syntax_getTailInfo___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
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
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateLast_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateLast_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Lean_Syntax_updateLast_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateLast___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateLast(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Lean_Syntax_updateLast___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_setTailInfoAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_setTailInfoAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_setTailInfoAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_setTailInfoAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_apply_1(x_5, x_1);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_4, x_7, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_2(x_2, x_10, x_11);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_4(x_3, x_13, x_14, x_15, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Syntax_setTailInfoAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_setTailInfoAux_match__2___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateLast___at_Lean_Syntax_setTailInfoAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_instInhabitedSyntax;
x_9 = lean_array_get(x_8, x_2, x_7);
lean_inc(x_1);
x_10 = l_Lean_Syntax_setTailInfoAux(x_1, x_9);
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
lean_object* l_Lean_Syntax_setTailInfoAux(lean_object* x_1, lean_object* x_2) {
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
x_8 = l___private_Init_Meta_0__Lean_Syntax_updateLast___at_Lean_Syntax_setTailInfoAux___spec__1(x_1, x_6, x_7);
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
x_17 = l___private_Init_Meta_0__Lean_Syntax_updateLast___at_Lean_Syntax_setTailInfoAux___spec__1(x_1, x_15, x_16);
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
lean_object* l_Lean_Syntax_setTailInfo_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_setTailInfo_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_setTailInfo_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_setTailInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_Lean_Syntax_setTailInfoAux(x_2, x_1);
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
lean_object* l_Lean_Syntax_unsetTrailing_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_unsetTrailing_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_unsetTrailing_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_unsetTrailing(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo(x_1);
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 2);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 2, x_6);
x_7 = l_Lean_Syntax_setTailInfo(x_1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_Lean_Syntax_setTailInfo(x_1, x_11);
return x_12;
}
}
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateFirst_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateFirst_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Lean_Syntax_updateFirst_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateFirst___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_fget(x_2, x_4);
lean_inc(x_3);
x_9 = lean_apply_1(x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_array_fset(x_2, x_4, x_14);
lean_dec(x_4);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_array_fset(x_2, x_4, x_16);
lean_dec(x_4);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateFirst(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Lean_Syntax_updateFirst___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateFirst___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Meta_0__Lean_Syntax_updateFirst___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_setHeadInfoAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_setHeadInfoAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_setHeadInfoAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_setHeadInfoAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_apply_1(x_5, x_1);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_4, x_7, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_2(x_2, x_10, x_11);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_4(x_3, x_13, x_14, x_15, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Syntax_setHeadInfoAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_setHeadInfoAux_match__2___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_updateFirst___at_Lean_Syntax_setHeadInfoAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
x_8 = l_Lean_Syntax_setHeadInfoAux(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_array_fset(x_2, x_3, x_13);
lean_dec(x_3);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_array_fset(x_2, x_3, x_15);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
}
lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Init_Meta_0__Lean_Syntax_updateFirst___at_Lean_Syntax_setHeadInfoAux___spec__1(x_1, x_6, x_7);
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
x_16 = lean_unsigned_to_nat(0u);
x_17 = l___private_Init_Meta_0__Lean_Syntax_updateFirst___at_Lean_Syntax_setHeadInfoAux___spec__1(x_1, x_15, x_16);
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
lean_object* l_Lean_Syntax_setHeadInfo_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_setHeadInfo_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_setHeadInfo_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_setHeadInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_Lean_Syntax_setHeadInfoAux(x_2, x_1);
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
lean_object* l_Lean_Syntax_setInfo_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
case 3:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_4(x_3, x_8, x_9, x_10, x_11);
return x_12;
}
default: 
{
lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_apply_1(x_4, x_1);
return x_13;
}
}
}
}
lean_object* l_Lean_Syntax_setInfo_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_setInfo_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_setInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
case 3:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 0);
lean_dec(x_8);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_12 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_10);
lean_ctor_set(x_12, 3, x_11);
return x_12;
}
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
lean_object* l_Lean_Syntax_replaceInfo_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_replaceInfo_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_replaceInfo_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Syntax_replaceInfo___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = x_4;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Syntax_replaceInfo(x_1, x_10);
x_12 = 1;
x_13 = x_3 + x_12;
x_14 = x_11;
x_15 = lean_array_uset(x_9, x_3, x_14);
x_3 = x_13;
x_4 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_Syntax_replaceInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = x_4;
x_9 = l_Array_mapMUnsafe_map___at_Lean_Syntax_replaceInfo___spec__1(x_1, x_6, x_7, x_8);
x_10 = x_9;
lean_ctor_set(x_2, 1, x_10);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_array_get_size(x_12);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = x_12;
x_17 = l_Array_mapMUnsafe_map___at_Lean_Syntax_replaceInfo___spec__1(x_1, x_14, x_15, x_16);
x_18 = x_17;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; 
x_20 = l_Lean_Syntax_setInfo(x_1, x_2);
return x_20;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Syntax_replaceInfo___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Syntax_replaceInfo___spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Lean_Syntax_copyInfo_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_copyInfo_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_copyInfo_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_copyInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_getHeadInfo(x_2);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Syntax_setHeadInfo(x_1, x_4);
return x_5;
}
}
}
lean_object* l_Lean_Syntax_copyInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_copyInfo(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_copyTailInfo_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_copyTailInfo_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_copyTailInfo_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_copyTailInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_getTailInfo(x_2);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Syntax_setTailInfo(x_1, x_4);
return x_5;
}
}
}
lean_object* l_Lean_Syntax_copyTailInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_copyTailInfo(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_mkAtom(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedSourceInfo___closed__1;
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
lean_object* l_Lean_expandMacros_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_expandMacros_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_expandMacros_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_expandMacros_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_apply_3(x_2, x_1, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_expandMacros_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_expandMacros_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_expandMacros___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_2 < x_1;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = x_3;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_12 = x_9;
lean_inc(x_4);
x_13 = l_Lean_expandMacros(x_12, x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = x_2 + x_16;
x_18 = x_14;
x_19 = lean_array_uset(x_11, x_2, x_18);
x_2 = x_17;
x_3 = x_19;
x_5 = x_15;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
static lean_object* _init_l_Lean_expandMacros___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_expandMacros(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_Lean_Macro_expandMacro_x3fImp(x_1, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = lean_array_get_size(x_5);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = x_5;
x_14 = lean_box_usize(x_12);
x_15 = l_Lean_expandMacros___boxed__const__1;
x_16 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_expandMacros___spec__1___boxed), 5, 3);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_13);
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 2);
x_21 = lean_ctor_get(x_2, 3);
x_22 = lean_ctor_get(x_2, 4);
x_23 = lean_ctor_get(x_2, 5);
x_24 = lean_nat_dec_eq(x_21, x_22);
if (x_24 == 0)
{
uint8_t x_25; 
lean_free_object(x_6);
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_1, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_1, 0);
lean_dec(x_27);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_21, x_28);
lean_dec(x_21);
lean_ctor_set(x_2, 3, x_29);
x_30 = x_16;
x_31 = lean_apply_2(x_30, x_2, x_9);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_ctor_set(x_1, 1, x_33);
lean_ctor_set(x_31, 0, x_1);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
lean_ctor_set(x_1, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_free_object(x_1);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_31);
if (x_37 == 0)
{
return x_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_31, 0);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_31);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_1);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_21, x_41);
lean_dec(x_21);
lean_ctor_set(x_2, 3, x_42);
x_43 = x_16;
x_44 = lean_apply_2(x_43, x_2, x_9);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_45);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_4);
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_52 = x_44;
} else {
 lean_dec_ref(x_44);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_free_object(x_2);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_4);
x_54 = l_Lean_maxRecDepthErrorMessage;
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_55);
return x_6;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_56 = lean_ctor_get(x_2, 0);
x_57 = lean_ctor_get(x_2, 1);
x_58 = lean_ctor_get(x_2, 2);
x_59 = lean_ctor_get(x_2, 3);
x_60 = lean_ctor_get(x_2, 4);
x_61 = lean_ctor_get(x_2, 5);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_2);
x_62 = lean_nat_dec_eq(x_59, x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_free_object(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_63 = x_1;
} else {
 lean_dec_ref(x_1);
 x_63 = lean_box(0);
}
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_59, x_64);
lean_dec(x_59);
x_66 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_66, 0, x_56);
lean_ctor_set(x_66, 1, x_57);
lean_ctor_set(x_66, 2, x_58);
lean_ctor_set(x_66, 3, x_65);
lean_ctor_set(x_66, 4, x_60);
lean_ctor_set(x_66, 5, x_61);
x_67 = x_16;
x_68 = lean_apply_2(x_67, x_66, x_9);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_63;
}
lean_ctor_set(x_72, 0, x_4);
lean_ctor_set(x_72, 1, x_69);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_63);
lean_dec(x_4);
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_76 = x_68;
} else {
 lean_dec_ref(x_68);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_16);
lean_dec(x_4);
x_78 = l_Lean_maxRecDepthErrorMessage;
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_79);
return x_6;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; size_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_80 = lean_ctor_get(x_6, 1);
lean_inc(x_80);
lean_dec(x_6);
x_81 = lean_array_get_size(x_5);
x_82 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_83 = x_5;
x_84 = lean_box_usize(x_82);
x_85 = l_Lean_expandMacros___boxed__const__1;
x_86 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_expandMacros___spec__1___boxed), 5, 3);
lean_closure_set(x_86, 0, x_84);
lean_closure_set(x_86, 1, x_85);
lean_closure_set(x_86, 2, x_83);
x_87 = lean_ctor_get(x_2, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_2, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_2, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_2, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_2, 4);
lean_inc(x_91);
x_92 = lean_ctor_get(x_2, 5);
lean_inc(x_92);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_93 = x_2;
} else {
 lean_dec_ref(x_2);
 x_93 = lean_box(0);
}
x_94 = lean_nat_dec_eq(x_90, x_91);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_95 = x_1;
} else {
 lean_dec_ref(x_1);
 x_95 = lean_box(0);
}
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_add(x_90, x_96);
lean_dec(x_90);
if (lean_is_scalar(x_93)) {
 x_98 = lean_alloc_ctor(0, 6, 0);
} else {
 x_98 = x_93;
}
lean_ctor_set(x_98, 0, x_87);
lean_ctor_set(x_98, 1, x_88);
lean_ctor_set(x_98, 2, x_89);
lean_ctor_set(x_98, 3, x_97);
lean_ctor_set(x_98, 4, x_91);
lean_ctor_set(x_98, 5, x_92);
x_99 = x_86;
x_100 = lean_apply_2(x_99, x_98, x_80);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_95;
}
lean_ctor_set(x_104, 0, x_4);
lean_ctor_set(x_104, 1, x_101);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_95);
lean_dec(x_4);
x_106 = lean_ctor_get(x_100, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_100, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_108 = x_100;
} else {
 lean_dec_ref(x_100);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_4);
x_110 = l_Lean_maxRecDepthErrorMessage;
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_1);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_80);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_113 = lean_ctor_get(x_6, 1);
lean_inc(x_113);
lean_dec(x_6);
x_114 = lean_ctor_get(x_7, 0);
lean_inc(x_114);
lean_dec(x_7);
x_1 = x_114;
x_3 = x_113;
goto _start;
}
}
else
{
uint8_t x_116; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_6);
if (x_116 == 0)
{
return x_6;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_6, 0);
x_118 = lean_ctor_get(x_6, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_6);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; 
lean_dec(x_2);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_1);
lean_ctor_set(x_120, 1, x_3);
return x_120;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_expandMacros___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at_Lean_expandMacros___spec__1(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_mkIdentFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_Syntax_getHeadInfo(x_1);
x_4 = l_Lean_Name_toString___closed__1;
lean_inc(x_2);
x_5 = l_Lean_Name_toStringWithSep(x_4, x_2);
x_6 = lean_string_utf8_byte_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_6);
x_9 = lean_box(0);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_instInhabitedSourceInfo___closed__1;
x_11 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_2);
lean_ctor_set(x_11, 3, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_2);
lean_ctor_set(x_13, 3, x_9);
return x_13;
}
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
static lean_object* _init_l_Lean_mkCIdentFrom___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_internal");
return x_1;
}
}
static lean_object* _init_l_Lean_mkCIdentFrom___closed__2() {
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
x_3 = l_Lean_Syntax_getHeadInfo(x_1);
x_4 = l_Lean_mkCIdentFrom___closed__2;
x_5 = l_Lean_reservedMacroScope;
lean_inc(x_2);
x_6 = l_Lean_addMacroScope(x_4, x_2, x_5);
x_7 = l_Lean_Name_toString___closed__1;
lean_inc(x_6);
x_8 = l_Lean_Name_toStringWithSep(x_7, x_6);
x_9 = lean_string_utf8_byte_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_instInhabitedSourceInfo___closed__1;
x_16 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_6);
lean_ctor_set(x_16, 3, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_6);
lean_ctor_set(x_18, 3, x_14);
return x_18;
}
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
lean_object* l_Lean_mkCIdent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_mkCIdentFrom(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_identToAtom_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_4(x_2, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Syntax_identToAtom_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_identToAtom_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_identToAtom(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_erase_macro_scopes(x_3);
x_5 = l_Lean_Name_toString___closed__1;
x_6 = l_Lean_Name_toStringWithSep(x_5, x_4);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
return x_1;
}
}
}
lean_object* lean_mk_syntax_ident(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l_Lean_Name_toString___closed__1;
lean_inc(x_1);
x_3 = l_Lean_Name_toStringWithSep(x_2, x_1);
x_4 = lean_string_utf8_byte_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_4);
x_7 = lean_box(0);
x_8 = l_Lean_instInhabitedSourceInfo___closed__1;
x_9 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_7);
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
lean_object* l_Lean_mkSepArray_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_mkSepArray_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkSepArray_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_mkSepArray_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_mkSepArray_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkSepArray_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 < x_3;
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_array_uget(x_2, x_4);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___closed__1;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_push(x_8, x_7);
x_14 = lean_box(0);
x_15 = lean_apply_3(x_10, x_13, x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
return x_16;
}
else
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = x_4 + x_18;
x_4 = x_19;
x_5 = x_17;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_1);
x_21 = lean_array_push(x_8, x_1);
x_22 = lean_array_push(x_21, x_7);
x_23 = lean_box(0);
x_24 = lean_apply_3(x_10, x_22, x_9, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
return x_25;
}
else
{
lean_object* x_26; size_t x_27; size_t x_28; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = 1;
x_28 = x_4 + x_27;
x_4 = x_28;
x_5 = x_26;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkSepArray___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkSepArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_5 = 0;
x_6 = l_Lean_mkSepArray___closed__1;
x_7 = l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1(x_2, x_1, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_mkSepArray___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkSepArray(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_mkOptionalNode_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_mkOptionalNode_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkOptionalNode_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_mkOptionalNode___closed__1() {
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
static lean_object* _init_l_Lean_mkOptionalNode___closed__2() {
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
lean_object* l_Lean_mkHole(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_myMacro____x40_Init_Notation___hyg_11811____closed__19;
x_3 = l_Lean_mkAtomFrom(x_1, x_2);
x_4 = l_Lean_mkOptionalNode___closed__2;
x_5 = lean_array_push(x_4, x_3);
x_6 = l_myMacro____x40_Init_Notation___hyg_11811____closed__18;
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
lean_object* l_Lean_Syntax_mkSep(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_mkSepArray(x_1, x_2);
x_4 = l_Lean_nullKind;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Syntax_mkSep___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_mkSep(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_mkAtom(x_1);
x_4 = l_Lean_mkSepArray(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_SepArray_ofElems___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_SepArray_ofElems(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_instCoeArraySyntaxSepArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElems___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_mkApp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Syntax_mkApp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_mkApp_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_mkApp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_mkApp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_Lean_nullKind;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = l_Lean_Syntax_mkApp___closed__1;
x_9 = lean_array_push(x_8, x_1);
x_10 = lean_array_push(x_9, x_7);
x_11 = l_myMacro____x40_Init_Notation___hyg_2094____closed__4;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Lean_Syntax_mkCApp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_Lean_mkCIdentFrom(x_3, x_1);
x_5 = l_Lean_Syntax_mkApp(x_4, x_2);
return x_5;
}
}
lean_object* l_Lean_Syntax_mkLit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Syntax_mkStrLit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_String_quote(x_1);
x_4 = l_Lean_strLitKind;
x_5 = l_Lean_Syntax_mkLit(x_4, x_3, x_2);
return x_5;
}
}
lean_object* l_Lean_Syntax_mkStrLit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_mkStrLit(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_mkNumLit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_numLitKind;
x_4 = l_Lean_Syntax_mkLit(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Syntax_mkScientificLit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_scientificLitKind;
x_4 = l_Lean_Syntax_mkLit(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeBinLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Meta_0__Lean_Syntax_decodeBinLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeOctalLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Meta_0__Lean_Syntax_decodeOctalLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeHexDigit(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeHexDigit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Meta_0__Lean_Syntax_decodeHexDigit(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeHexLitAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeHexLitAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Lean_Syntax_decodeHexLitAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeHexLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l___private_Init_Meta_0__Lean_Syntax_decodeHexDigit(x_1, x_2);
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
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Meta_0__Lean_Syntax_decodeHexLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeDecimalLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Meta_0__Lean_Syntax_decodeDecimalLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Syntax_decodeNatLitVal_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object* x_1) {
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
x_10 = l___private_Init_Meta_0__Lean_Syntax_decodeDecimalLitAux(x_1, x_3, x_3);
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
uint32_t x_18; uint8_t x_19; 
x_18 = 98;
x_19 = x_13 == x_18;
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
x_28 = l___private_Init_Meta_0__Lean_Syntax_decodeDecimalLitAux(x_1, x_3, x_3);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_unsigned_to_nat(2u);
x_30 = l___private_Init_Meta_0__Lean_Syntax_decodeOctalLitAux(x_1, x_29, x_3);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_unsigned_to_nat(2u);
x_32 = l___private_Init_Meta_0__Lean_Syntax_decodeOctalLitAux(x_1, x_31, x_3);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_unsigned_to_nat(2u);
x_34 = l___private_Init_Meta_0__Lean_Syntax_decodeBinLitAux(x_1, x_33, x_3);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_unsigned_to_nat(2u);
x_36 = l___private_Init_Meta_0__Lean_Syntax_decodeBinLitAux(x_1, x_35, x_3);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_unsigned_to_nat(2u);
x_38 = l___private_Init_Meta_0__Lean_Syntax_decodeHexLitAux(x_1, x_37, x_3);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_unsigned_to_nat(2u);
x_40 = l___private_Init_Meta_0__Lean_Syntax_decodeHexLitAux(x_1, x_39, x_3);
return x_40;
}
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Syntax_decodeNatLitVal_x3f___closed__1;
return x_41;
}
}
}
else
{
lean_object* x_42; 
lean_dec(x_2);
x_42 = lean_box(0);
return x_42;
}
}
}
lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_decodeNatLitVal_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_isLit_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_isLit_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isLit_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_isLit_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_isLit_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isLit_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_isLit_x3f(lean_object* x_1, lean_object* x_2) {
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
x_11 = l_Lean_instInhabitedSyntax;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_11, x_4, x_12);
if (lean_obj_tag(x_13) == 2)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
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
lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_isLit_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_isNatLitAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_isNatLitAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Lean_Syntax_isNatLitAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_isLit_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Syntax_decodeNatLitVal_x3f(x_5);
lean_dec(x_5);
return x_6;
}
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_isNatLitAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_1, x_2);
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
x_3 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_2, x_1);
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
x_3 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_2, x_1);
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
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_string_utf8_at_end(x_1, x_2);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get(x_1, x_2);
x_9 = 48;
x_10 = x_9 <= x_8;
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
}
else
{
uint32_t x_12; uint8_t x_13; 
x_12 = 57;
x_13 = x_8 <= x_12;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_16 = lean_unsigned_to_nat(10u);
x_17 = lean_nat_mul(x_16, x_6);
lean_dec(x_6);
x_18 = lean_uint32_to_nat(x_8);
x_19 = lean_nat_add(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(48u);
x_21 = lean_nat_sub(x_19, x_20);
lean_dec(x_19);
x_2 = x_15;
x_6 = x_21;
goto _start;
}
}
}
else
{
lean_dec(x_2);
if (x_5 == 0)
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_4, x_6);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_nat_sub(x_4, x_6);
lean_dec(x_6);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_nat_sub(x_6, x_4);
lean_dec(x_6);
x_31 = lean_box(x_5);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_3);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_nat_add(x_6, x_4);
lean_dec(x_6);
x_36 = lean_box(x_5);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_3);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(x_1, x_2, x_3, x_4, x_7, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_string_utf8_get(x_1, x_2);
x_6 = 45;
x_7 = x_5 == x_6;
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(x_1, x_2, x_3, x_4, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_12 = 1;
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(x_1, x_11, x_3, x_4, x_12, x_13);
return x_14;
}
}
}
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_2);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_2);
x_7 = 48;
x_8 = x_7 <= x_6;
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 101;
x_10 = x_6 == x_9;
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 69;
x_12 = x_6 == x_11;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_15 = l_Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(x_1, x_14, x_3, x_4);
lean_dec(x_4);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_17 = l_Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(x_1, x_16, x_3, x_4);
lean_dec(x_4);
return x_17;
}
}
else
{
uint32_t x_18; uint8_t x_19; 
x_18 = 57;
x_19 = x_6 <= x_18;
if (x_19 == 0)
{
uint32_t x_20; uint8_t x_21; 
x_20 = 101;
x_21 = x_6 == x_20;
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 69;
x_23 = x_6 == x_22;
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_box(0);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_26 = l_Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(x_1, x_25, x_3, x_4);
lean_dec(x_4);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_28 = l_Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(x_1, x_27, x_3, x_4);
lean_dec(x_4);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_30 = lean_unsigned_to_nat(10u);
x_31 = lean_nat_mul(x_30, x_3);
lean_dec(x_3);
x_32 = lean_uint32_to_nat(x_6);
x_33 = lean_nat_add(x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
x_34 = lean_unsigned_to_nat(48u);
x_35 = lean_nat_sub(x_33, x_34);
lean_dec(x_33);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_4, x_36);
lean_dec(x_4);
x_2 = x_29;
x_3 = x_35;
x_4 = x_37;
goto _start;
}
}
}
else
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_2);
x_39 = 1;
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_4);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_3);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint32_t x_8; uint8_t x_9; 
x_8 = 46;
x_9 = x_5 == x_8;
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 101;
x_11 = x_5 == x_10;
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 69;
x_13 = x_5 == x_12;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(x_1, x_15, x_3, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(x_1, x_18, x_3, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(x_1, x_21, x_3, x_22);
return x_23;
}
}
else
{
uint32_t x_24; uint8_t x_25; 
x_24 = 57;
x_25 = x_5 <= x_24;
if (x_25 == 0)
{
uint32_t x_26; uint8_t x_27; 
x_26 = 46;
x_27 = x_5 == x_26;
if (x_27 == 0)
{
uint32_t x_28; uint8_t x_29; 
x_28 = 101;
x_29 = x_5 == x_28;
if (x_29 == 0)
{
uint32_t x_30; uint8_t x_31; 
x_30 = 69;
x_31 = x_5 == x_30;
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_box(0);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(x_1, x_33, x_3, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(x_1, x_36, x_3, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(x_1, x_39, x_3, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_43 = lean_unsigned_to_nat(10u);
x_44 = lean_nat_mul(x_43, x_3);
lean_dec(x_3);
x_45 = lean_uint32_to_nat(x_5);
x_46 = lean_nat_add(x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
x_47 = lean_unsigned_to_nat(48u);
x_48 = lean_nat_sub(x_46, x_47);
lean_dec(x_46);
x_2 = x_42;
x_3 = x_48;
goto _start;
}
}
}
else
{
lean_object* x_50; 
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_box(0);
return x_50;
}
}
}
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_decodeScientificLitVal_x3f_decode(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_string_length(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = lean_string_utf8_get(x_1, x_3);
x_6 = l_Char_isDigit(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lean_Syntax_decodeScientificLitVal_x3f_decode(x_1, x_3, x_3);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
}
}
lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_decodeScientificLitVal_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_isScientificLit_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_isScientificLit_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isScientificLit_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_scientificLitKind;
x_3 = l_Lean_Syntax_isLit_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Syntax_decodeScientificLitVal_x3f(x_5);
lean_dec(x_5);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isScientificLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_isIdOrAtom_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
case 3:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_4(x_3, x_8, x_9, x_10, x_11);
return x_12;
}
default: 
{
lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_apply_1(x_4, x_1);
return x_13;
}
}
}
}
lean_object* l_Lean_Syntax_isIdOrAtom_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isIdOrAtom_x3f_match__1___rarg), 4, 0);
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
lean_object* l_Lean_Syntax_toNat_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_toNat_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_toNat_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_toNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_numLitKind;
x_3 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_2, x_1);
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
lean_object* l_Lean_Syntax_decodeQuotedChar_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_decodeQuotedChar_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_decodeQuotedChar_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_decodeQuotedChar_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_decodeQuotedChar_match__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__5___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_decodeQuotedChar_match__5___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__6___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_decodeQuotedChar_match__6___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 9;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 13;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 39;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 34;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 92;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object* x_1, lean_object* x_2) {
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
x_11 = 114;
x_12 = x_3 == x_11;
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 110;
x_14 = x_3 == x_13;
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 116;
x_16 = x_3 == x_15;
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 120;
x_18 = x_3 == x_17;
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 117;
x_20 = x_3 == x_19;
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_4);
x_21 = lean_box(0);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = l___private_Init_Meta_0__Lean_Syntax_decodeHexDigit(x_1, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_box(0);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Init_Meta_0__Lean_Syntax_decodeHexDigit(x_1, x_26);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec(x_25);
x_28 = lean_box(0);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Init_Meta_0__Lean_Syntax_decodeHexDigit(x_1, x_31);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_25);
x_33 = lean_box(0);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l___private_Init_Meta_0__Lean_Syntax_decodeHexDigit(x_1, x_36);
lean_dec(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_25);
x_38 = lean_box(0);
return x_38;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_37, 0);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint32_t x_51; lean_object* x_52; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_unsigned_to_nat(16u);
x_44 = lean_nat_mul(x_43, x_25);
lean_dec(x_25);
x_45 = lean_nat_add(x_44, x_30);
lean_dec(x_30);
lean_dec(x_44);
x_46 = lean_nat_mul(x_43, x_45);
lean_dec(x_45);
x_47 = lean_nat_add(x_46, x_35);
lean_dec(x_35);
lean_dec(x_46);
x_48 = lean_nat_mul(x_43, x_47);
lean_dec(x_47);
x_49 = lean_nat_add(x_48, x_42);
lean_dec(x_42);
lean_dec(x_48);
x_50 = l_Char_ofNat(x_49);
x_51 = lean_unbox_uint32(x_50);
lean_dec(x_50);
x_52 = lean_box_uint32(x_51);
lean_ctor_set(x_40, 0, x_52);
return x_37;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint32_t x_63; lean_object* x_64; lean_object* x_65; 
x_53 = lean_ctor_get(x_40, 0);
x_54 = lean_ctor_get(x_40, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_40);
x_55 = lean_unsigned_to_nat(16u);
x_56 = lean_nat_mul(x_55, x_25);
lean_dec(x_25);
x_57 = lean_nat_add(x_56, x_30);
lean_dec(x_30);
lean_dec(x_56);
x_58 = lean_nat_mul(x_55, x_57);
lean_dec(x_57);
x_59 = lean_nat_add(x_58, x_35);
lean_dec(x_35);
lean_dec(x_58);
x_60 = lean_nat_mul(x_55, x_59);
lean_dec(x_59);
x_61 = lean_nat_add(x_60, x_53);
lean_dec(x_53);
lean_dec(x_60);
x_62 = l_Char_ofNat(x_61);
x_63 = lean_unbox_uint32(x_62);
lean_dec(x_62);
x_64 = lean_box_uint32(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_54);
lean_ctor_set(x_37, 0, x_65);
return x_37;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint32_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_66 = lean_ctor_get(x_37, 0);
lean_inc(x_66);
lean_dec(x_37);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = lean_unsigned_to_nat(16u);
x_71 = lean_nat_mul(x_70, x_25);
lean_dec(x_25);
x_72 = lean_nat_add(x_71, x_30);
lean_dec(x_30);
lean_dec(x_71);
x_73 = lean_nat_mul(x_70, x_72);
lean_dec(x_72);
x_74 = lean_nat_add(x_73, x_35);
lean_dec(x_35);
lean_dec(x_73);
x_75 = lean_nat_mul(x_70, x_74);
lean_dec(x_74);
x_76 = lean_nat_add(x_75, x_67);
lean_dec(x_67);
lean_dec(x_75);
x_77 = l_Char_ofNat(x_76);
x_78 = lean_unbox_uint32(x_77);
lean_dec(x_77);
x_79 = lean_box_uint32(x_78);
if (lean_is_scalar(x_69)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_69;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_68);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
}
}
else
{
lean_object* x_82; 
x_82 = l___private_Init_Meta_0__Lean_Syntax_decodeHexDigit(x_1, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_box(0);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l___private_Init_Meta_0__Lean_Syntax_decodeHexDigit(x_1, x_86);
lean_dec(x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
lean_dec(x_85);
x_88 = lean_box(0);
return x_88;
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_87, 0);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint32_t x_97; lean_object* x_98; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_unsigned_to_nat(16u);
x_94 = lean_nat_mul(x_93, x_85);
lean_dec(x_85);
x_95 = lean_nat_add(x_94, x_92);
lean_dec(x_92);
lean_dec(x_94);
x_96 = l_Char_ofNat(x_95);
x_97 = lean_unbox_uint32(x_96);
lean_dec(x_96);
x_98 = lean_box_uint32(x_97);
lean_ctor_set(x_90, 0, x_98);
return x_87;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint32_t x_105; lean_object* x_106; lean_object* x_107; 
x_99 = lean_ctor_get(x_90, 0);
x_100 = lean_ctor_get(x_90, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_90);
x_101 = lean_unsigned_to_nat(16u);
x_102 = lean_nat_mul(x_101, x_85);
lean_dec(x_85);
x_103 = lean_nat_add(x_102, x_99);
lean_dec(x_99);
lean_dec(x_102);
x_104 = l_Char_ofNat(x_103);
x_105 = lean_unbox_uint32(x_104);
lean_dec(x_104);
x_106 = lean_box_uint32(x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_100);
lean_ctor_set(x_87, 0, x_107);
return x_87;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint32_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_108 = lean_ctor_get(x_87, 0);
lean_inc(x_108);
lean_dec(x_87);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
x_112 = lean_unsigned_to_nat(16u);
x_113 = lean_nat_mul(x_112, x_85);
lean_dec(x_85);
x_114 = lean_nat_add(x_113, x_109);
lean_dec(x_109);
lean_dec(x_113);
x_115 = l_Char_ofNat(x_114);
x_116 = lean_unbox_uint32(x_115);
lean_dec(x_115);
x_117 = lean_box_uint32(x_116);
if (lean_is_scalar(x_111)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_111;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_110);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_4);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_4);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_4);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_4);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_4);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_4);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_decodeQuotedChar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_decodeStrLitAux_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_decodeStrLitAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_decodeStrLitAux_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t x_8; 
x_8 = lean_string_utf8_at_end(x_1, x_5);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 92;
x_10 = x_4 == x_9;
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_string_push(x_3, x_4);
x_2 = x_5;
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Syntax_decodeQuotedChar(x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint32_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unbox_uint32(x_16);
lean_dec(x_16);
x_19 = lean_string_push(x_3, x_18);
x_2 = x_17;
x_3 = x_19;
goto _start;
}
}
}
else
{
lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_3);
x_21 = lean_box(0);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_5);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_3);
return x_22;
}
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
x_3 = l_Lean_instInhabitedParserDescr___closed__1;
x_4 = l_Lean_Syntax_decodeStrLitAux(x_1, x_2, x_3);
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
lean_object* l_Lean_Syntax_isStrLit_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_isStrLit_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isStrLit_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_strLitKind;
x_3 = l_Lean_Syntax_isLit_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_instInhabitedParserDescr___closed__1;
x_8 = l_Lean_Syntax_decodeStrLitAux(x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
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
lean_object* l_Lean_Syntax_decodeCharLit_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_decodeCharLit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_decodeCharLit_match__1___rarg), 2, 0);
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
x_9 = l_Lean_Syntax_decodeQuotedChar(x_1, x_8);
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
lean_object* l_Lean_Syntax_isCharLit_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_isCharLit_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isCharLit_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_charLitKind;
x_3 = l_Lean_Syntax_isLit_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Syntax_decodeCharLit(x_5);
lean_dec(x_5);
return x_6;
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
lean_object* l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_decodeNameLitAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_3, x_2);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = lean_string_utf8_get(x_1, x_3);
x_6 = l_Lean_isIdRest(x_5);
if (x_6 == 0)
{
return x_3;
}
else
{
lean_object* x_7; 
x_7 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_7;
goto _start;
}
}
else
{
return x_3;
}
}
}
lean_object* l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_decodeNameLitAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_3, x_2);
if (x_4 == 0)
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_string_utf8_get(x_1, x_3);
x_6 = l_Lean_idEndEscape;
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_8;
goto _start;
}
else
{
return x_3;
}
}
else
{
return x_3;
}
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeNameLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint32_t x_15; uint32_t x_16; uint8_t x_17; 
x_15 = lean_string_utf8_get(x_1, x_2);
x_16 = l_Lean_idBeginEscape;
x_17 = x_15 == x_16;
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_isIdFirst(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_string_utf8_byte_size(x_1);
lean_inc(x_2);
x_21 = l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_decodeNameLitAux___spec__1(x_1, x_20, x_2);
lean_dec(x_20);
x_22 = lean_string_utf8_extract(x_1, x_2, x_21);
lean_dec(x_2);
x_23 = lean_name_mk_string(x_3, x_22);
x_4 = x_21;
x_5 = x_23;
goto block_14;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint32_t x_27; uint32_t x_28; uint8_t x_29; 
x_24 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_25 = lean_string_utf8_byte_size(x_1);
lean_inc(x_24);
x_26 = l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_decodeNameLitAux___spec__2(x_1, x_25, x_24);
lean_dec(x_25);
x_27 = lean_string_utf8_get(x_1, x_26);
x_28 = l_Lean_idEndEscape;
x_29 = x_27 == x_28;
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_3);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_string_utf8_next(x_1, x_26);
x_32 = lean_string_utf8_extract(x_1, x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
x_33 = lean_name_mk_string(x_3, x_32);
x_4 = x_31;
x_5 = x_33;
goto block_14;
}
}
block_14:
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_4);
x_7 = 46;
x_8 = x_6 == x_7;
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_string_utf8_at_end(x_1, x_4);
lean_dec(x_4);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_2 = x_12;
x_3 = x_5;
goto _start;
}
}
}
}
lean_object* l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_decodeNameLitAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_decodeNameLitAux___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_decodeNameLitAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_decodeNameLitAux___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeNameLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Meta_0__Lean_Syntax_decodeNameLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_decodeNameLit(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 96;
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_box(0);
x_9 = l___private_Init_Meta_0__Lean_Syntax_decodeNameLitAux(x_1, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Syntax_decodeNameLit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_decodeNameLit(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_isNameLit_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_isNameLit_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isNameLit_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_nameLitKind;
x_3 = l_Lean_Syntax_isLit_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Syntax_decodeNameLit(x_5);
lean_dec(x_5);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isNameLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_hasArgs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_hasArgs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_hasArgs_match__1___rarg), 3, 0);
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
lean_object* l_Lean_Syntax_identToStrLit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_4(x_2, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Syntax_identToStrLit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_identToStrLit_match__1___rarg), 3, 0);
return x_2;
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
x_5 = l_Lean_Name_toStringWithSep(x_4, x_3);
x_6 = l_Lean_Syntax_mkStrLit(x_5, x_2);
lean_dec(x_5);
return x_6;
}
else
{
return x_1;
}
}
}
lean_object* l_Lean_Syntax_strLitToAtom_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_strLitToAtom_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_strLitToAtom_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_strLitToAtom_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_strLitToAtom_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_strLitToAtom_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_strLitToAtom___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Meta");
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_strLitToAtom___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Syntax.strLitToAtom");
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_strLitToAtom___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unreachable code has been reached");
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_strLitToAtom___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Syntax_strLitToAtom___closed__1;
x_2 = l_Lean_Syntax_strLitToAtom___closed__2;
x_3 = lean_unsigned_to_nat(559u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
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
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Syntax_getHeadInfo(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = l_Lean_instInhabitedSyntax;
x_6 = l_Lean_Syntax_strLitToAtom___closed__4;
x_7 = lean_panic_fn(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
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
lean_object* l_Lean_Syntax_isAtom_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_isAtom_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isAtom_match__1___rarg), 3, 0);
return x_2;
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
lean_object* l_Lean_Syntax_isToken_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_isToken_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isToken_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Syntax_isToken(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_String_trim(x_3);
x_5 = l_String_trim(x_1);
x_6 = lean_string_dec_eq(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
lean_object* l_Lean_Syntax_isToken___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_isToken(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_isIdent_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_4(x_2, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Syntax_isIdent_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isIdent_match__1___rarg), 3, 0);
return x_2;
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
lean_object* l_Lean_Syntax_getId_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_4(x_2, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Syntax_getId_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_getId_match__1___rarg), 3, 0);
return x_2;
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
lean_object* l_Lean_Syntax_isNone_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
default: 
{
lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_apply_1(x_4, x_1);
return x_10;
}
}
}
}
lean_object* l_Lean_Syntax_isNone_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isNone_match__1___rarg), 4, 0);
return x_2;
}
}
uint8_t l_Lean_Syntax_isNone(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_nullKind;
x_6 = lean_name_eq(x_3, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
default: 
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
}
lean_object* l_Lean_Syntax_isNone___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isNone(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_getOptional_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_getOptional_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_getOptional_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_nullKind;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_instInhabitedSyntax;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_11, x_3, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; 
x_15 = lean_box(0);
return x_15;
}
}
}
lean_object* l_Lean_Syntax_getOptional_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getOptional_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_getOptionalIdent_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_getOptionalIdent_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_getOptionalIdent_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getOptional_x3f(x_1);
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
x_6 = l_Lean_Syntax_getId(x_5);
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
x_8 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getOptionalIdent_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_findAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_apply_3(x_2, x_1, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_findAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_findAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_findAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 < x_4;
if (x_7 == 0)
{
lean_dec(x_1);
lean_inc(x_6);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
x_9 = l_Lean_Syntax_findAux(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = x_5 + x_10;
{
size_t _tmp_4 = x_11;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
lean_object* l_Lean_Syntax_findAux(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_4 = lean_apply_1(x_1, x_2);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_array_get_size(x_3);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = l_Array_findSomeM_x3f___rarg___closed__1;
x_11 = l_Array_forInUnsafe_loop___at_Lean_Syntax_findAux___spec__1(x_1, x_10, x_3, x_8, x_9, x_10);
lean_dec(x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
return x_6;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_inc(x_2);
x_17 = lean_apply_1(x_1, x_2);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_2);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_2);
return x_20;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_findAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forInUnsafe_loop___at_Lean_Syntax_findAux___spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Syntax_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_findAux(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instQuoteSyntax() {
_start:
{
lean_object* x_1; 
x_1 = l_Applicative_seqRight___default___rarg___closed__1;
return x_1;
}
}
lean_object* l_Lean_instQuoteBool_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_instQuoteBool_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instQuoteBool_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_instQuoteBool_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_instQuoteBool_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_instQuoteBool___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Bool");
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteBool___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instQuoteBool___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instQuoteBool___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instQuoteBool___closed__2;
x_2 = l_instReprBool___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instQuoteBool___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instQuoteBool___closed__3;
x_3 = l_Lean_mkCIdentFrom(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instQuoteBool___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instQuoteBool___closed__2;
x_2 = l_instReprBool___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instQuoteBool___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instQuoteBool___closed__5;
x_3 = l_Lean_mkCIdentFrom(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_instQuoteBool(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lean_instQuoteBool___closed__4;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_instQuoteBool___closed__6;
return x_3;
}
}
}
lean_object* l_Lean_instQuoteBool___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_instQuoteBool(x_2);
return x_3;
}
}
lean_object* l_Lean_instQuoteString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedSourceInfo___closed__1;
x_3 = l_Lean_Syntax_mkStrLit(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_instQuoteString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instQuoteString(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_instQuoteNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Nat_repr(x_1);
x_3 = l_Lean_numLitKind;
x_4 = l_Lean_instInhabitedSourceInfo___closed__1;
x_5 = l_Lean_Syntax_mkLit(x_3, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_instQuoteSubstring___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("String");
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteSubstring___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instQuoteSubstring___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instQuoteSubstring___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("toSubstring");
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteSubstring___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instQuoteSubstring___closed__2;
x_2 = l_Lean_instQuoteSubstring___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_instQuoteSubstring(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_string_utf8_extract(x_2, x_3, x_4);
x_6 = l_Lean_instInhabitedSourceInfo___closed__1;
x_7 = l_Lean_Syntax_mkStrLit(x_5, x_6);
lean_dec(x_5);
x_8 = l_Lean_mkOptionalNode___closed__2;
x_9 = lean_array_push(x_8, x_7);
x_10 = l_Lean_instQuoteSubstring___closed__4;
x_11 = l_Lean_Syntax_mkCApp(x_10, x_9);
return x_11;
}
}
lean_object* l_Lean_instQuoteSubstring___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instQuoteSubstring(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Meta_0__Lean_quoteName_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_10 = lean_box_usize(x_9);
x_11 = lean_apply_3(x_3, x_7, x_8, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_15 = lean_box_usize(x_14);
x_16 = lean_apply_3(x_4, x_12, x_13, x_15);
return x_16;
}
}
}
}
lean_object* l___private_Init_Meta_0__Lean_quoteName_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Lean_quoteName_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l___private_Init_Meta_0__Lean_quoteName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Name");
return x_1;
}
}
static lean_object* _init_l___private_Init_Meta_0__Lean_quoteName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__2;
x_2 = l___private_Init_Meta_0__Lean_quoteName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_Meta_0__Lean_quoteName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("anonymous");
return x_1;
}
}
static lean_object* _init_l___private_Init_Meta_0__Lean_quoteName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Meta_0__Lean_quoteName___closed__2;
x_2 = l___private_Init_Meta_0__Lean_quoteName___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_Meta_0__Lean_quoteName___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Meta_0__Lean_quoteName___closed__4;
x_3 = l_Lean_mkCIdentFrom(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_Meta_0__Lean_quoteName___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkStr");
return x_1;
}
}
static lean_object* _init_l___private_Init_Meta_0__Lean_quoteName___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Meta_0__Lean_quoteName___closed__2;
x_2 = l___private_Init_Meta_0__Lean_quoteName___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_Meta_0__Lean_quoteName___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkNum");
return x_1;
}
}
static lean_object* _init_l___private_Init_Meta_0__Lean_quoteName___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Meta_0__Lean_quoteName___closed__2;
x_2 = l___private_Init_Meta_0__Lean_quoteName___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Meta_0__Lean_quoteName(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l___private_Init_Meta_0__Lean_quoteName___closed__5;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l___private_Init_Meta_0__Lean_quoteName(x_3);
x_6 = l_Lean_instInhabitedSourceInfo___closed__1;
x_7 = l_Lean_Syntax_mkStrLit(x_4, x_6);
lean_dec(x_4);
x_8 = l_Lean_Syntax_mkApp___closed__1;
x_9 = lean_array_push(x_8, x_5);
x_10 = lean_array_push(x_9, x_7);
x_11 = l___private_Init_Meta_0__Lean_quoteName___closed__7;
x_12 = l_Lean_Syntax_mkCApp(x_11, x_10);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l___private_Init_Meta_0__Lean_quoteName(x_13);
x_16 = l_Nat_repr(x_14);
x_17 = l_Lean_numLitKind;
x_18 = l_Lean_instInhabitedSourceInfo___closed__1;
x_19 = l_Lean_Syntax_mkLit(x_17, x_16, x_18);
x_20 = l_Lean_Syntax_mkApp___closed__1;
x_21 = lean_array_push(x_20, x_15);
x_22 = lean_array_push(x_21, x_19);
x_23 = l___private_Init_Meta_0__Lean_quoteName___closed__9;
x_24 = l_Lean_Syntax_mkCApp(x_23, x_22);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_instQuoteName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Lean_quoteName), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteName() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instQuoteName___closed__1;
return x_1;
}
}
lean_object* l_Lean_instQuoteProd_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_instQuoteProd_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_instQuoteProd_match__1___rarg), 2, 0);
return x_4;
}
}
static lean_object* _init_l_Lean_instQuoteProd___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mk");
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteProd___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_myMacro____x40_Init_Notation___hyg_2351____closed__4;
x_2 = l_Lean_instQuoteProd___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_instQuoteProd___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_apply_1(x_2, x_5);
x_8 = l_Lean_Syntax_mkApp___closed__1;
x_9 = lean_array_push(x_8, x_6);
x_10 = lean_array_push(x_9, x_7);
x_11 = l_Lean_instQuoteProd___rarg___closed__2;
x_12 = l_Lean_Syntax_mkCApp(x_11, x_10);
return x_12;
}
}
lean_object* l_Lean_instQuoteProd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instQuoteProd___rarg), 3, 0);
return x_3;
}
}
lean_object* l___private_Init_Meta_0__Lean_quoteList_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Init_Meta_0__Lean_quoteList_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Lean_quoteList_match__1___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l___private_Init_Meta_0__Lean_quoteList___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_myMacro____x40_Init_Notation___hyg_13581____closed__7;
x_3 = l_Lean_mkCIdentFrom(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Meta_0__Lean_quoteList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = l___private_Init_Meta_0__Lean_quoteList___rarg___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = lean_apply_1(x_1, x_4);
x_7 = l___private_Init_Meta_0__Lean_quoteList___rarg(x_1, x_5);
x_8 = l_Lean_Syntax_mkApp___closed__1;
x_9 = lean_array_push(x_8, x_6);
x_10 = lean_array_push(x_9, x_7);
x_11 = l_myMacro____x40_Init_Notation___hyg_9172____closed__7;
x_12 = l_Lean_Syntax_mkCApp(x_11, x_10);
return x_12;
}
}
}
lean_object* l___private_Init_Meta_0__Lean_quoteList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Lean_quoteList___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_instQuoteList___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Lean_quoteList___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_instQuoteList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instQuoteList___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_instQuoteArray___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_array_to_list(lean_box(0), x_2);
x_4 = l___private_Init_Meta_0__Lean_quoteList___rarg(x_1, x_3);
x_5 = l_Lean_mkOptionalNode___closed__2;
x_6 = lean_array_push(x_5, x_4);
x_7 = l_myMacro____x40_Init_Data_Array_Basic___hyg_3426____closed__5;
x_8 = l_Lean_Syntax_mkCApp(x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_instQuoteArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instQuoteArray___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Init_Meta_0__Lean_quoteOption_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Init_Meta_0__Lean_quoteOption_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Lean_quoteOption_match__1___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Option");
return x_1;
}
}
static lean_object* _init_l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__2;
x_2 = l_instReprOption___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__3;
x_2 = lean_mk_syntax_ident(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("some");
return x_1;
}
}
static lean_object* _init_l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__2;
x_2 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Meta_0__Lean_quoteOption___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__4;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = l_Lean_mkOptionalNode___closed__2;
x_7 = lean_array_push(x_6, x_5);
x_8 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__6;
x_9 = l_Lean_Syntax_mkCApp(x_8, x_7);
return x_9;
}
}
}
lean_object* l___private_Init_Meta_0__Lean_quoteOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Lean_quoteOption___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Option_hasQuote___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Lean_quoteOption___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Option_hasQuote(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_evalPrec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected precedence");
return x_1;
}
}
lean_object* l_Lean_evalPrec(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get(x_2, 4);
x_10 = lean_ctor_get(x_2, 5);
x_11 = lean_nat_dec_eq(x_8, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_8, x_12);
lean_dec(x_8);
lean_ctor_set(x_2, 3, x_13);
lean_inc(x_2);
x_14 = l_Lean_expandMacros(x_1, x_2, x_3);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_numLitKind___closed__2;
lean_inc(x_16);
x_19 = l_Lean_Syntax_isOfKind(x_16, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_14);
x_20 = l_Lean_evalPrec___closed__1;
x_21 = l_Lean_Macro_throwErrorAt___rarg(x_16, x_20, x_2, x_17);
lean_dec(x_16);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_22 = l_Lean_numLitKind;
x_23 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_22, x_16);
lean_dec(x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = l_Lean_numLitKind___closed__2;
lean_inc(x_26);
x_29 = l_Lean_Syntax_isOfKind(x_26, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_evalPrec___closed__1;
x_31 = l_Lean_Macro_throwErrorAt___rarg(x_26, x_30, x_2, x_27);
lean_dec(x_26);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_2);
x_32 = l_Lean_numLitKind;
x_33 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_32, x_26);
lean_dec(x_26);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_14);
if (x_38 == 0)
{
return x_14;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_14, 0);
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_14);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_free_object(x_2);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_42 = l_Lean_maxRecDepthErrorMessage;
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_3);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
x_47 = lean_ctor_get(x_2, 2);
x_48 = lean_ctor_get(x_2, 3);
x_49 = lean_ctor_get(x_2, 4);
x_50 = lean_ctor_get(x_2, 5);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_2);
x_51 = lean_nat_dec_eq(x_48, x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_48, x_52);
lean_dec(x_48);
x_54 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_46);
lean_ctor_set(x_54, 2, x_47);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set(x_54, 4, x_49);
lean_ctor_set(x_54, 5, x_50);
lean_inc(x_54);
x_55 = l_Lean_expandMacros(x_1, x_54, x_3);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
x_59 = l_Lean_numLitKind___closed__2;
lean_inc(x_56);
x_60 = l_Lean_Syntax_isOfKind(x_56, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_58);
x_61 = l_Lean_evalPrec___closed__1;
x_62 = l_Lean_Macro_throwErrorAt___rarg(x_56, x_61, x_54, x_57);
lean_dec(x_56);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_54);
x_63 = l_Lean_numLitKind;
x_64 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_63, x_56);
lean_dec(x_56);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_58)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_58;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_57);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
lean_dec(x_64);
if (lean_is_scalar(x_58)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_58;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_57);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_54);
x_69 = lean_ctor_get(x_55, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_55, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_71 = x_55;
} else {
 lean_dec_ref(x_55);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
x_73 = l_Lean_maxRecDepthErrorMessage;
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_3);
return x_75;
}
}
}
}
lean_object* l_Lean_myMacro____x40_Init_Meta___hyg_3942_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Syntax_addPrec___closed__8;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
lean_inc(x_2);
x_12 = l_Lean_evalPrec(x_9, x_2, x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_evalPrec(x_11, x_2, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_17);
lean_dec(x_13);
x_19 = l_Nat_repr(x_18);
x_20 = l_Lean_numLitKind;
x_21 = l_Lean_instInhabitedSourceInfo___closed__1;
x_22 = l_Lean_Syntax_mkLit(x_20, x_19, x_21);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_nat_add(x_13, x_23);
lean_dec(x_23);
lean_dec(x_13);
x_26 = l_Nat_repr(x_25);
x_27 = l_Lean_numLitKind;
x_28 = l_Lean_instInhabitedSourceInfo___closed__1;
x_29 = l_Lean_Syntax_mkLit(x_27, x_26, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_13);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_11);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_12);
if (x_35 == 0)
{
return x_12;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_12, 0);
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_12);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
lean_object* l_Lean_myMacro____x40_Init_Meta___hyg_4040_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Syntax_subPrec___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
lean_inc(x_2);
x_12 = l_Lean_evalPrec(x_9, x_2, x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_evalPrec(x_11, x_2, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_nat_sub(x_13, x_17);
lean_dec(x_17);
lean_dec(x_13);
x_19 = l_Nat_repr(x_18);
x_20 = l_Lean_numLitKind;
x_21 = l_Lean_instInhabitedSourceInfo___closed__1;
x_22 = l_Lean_Syntax_mkLit(x_20, x_19, x_21);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_nat_sub(x_13, x_23);
lean_dec(x_23);
lean_dec(x_13);
x_26 = l_Nat_repr(x_25);
x_27 = l_Lean_numLitKind;
x_28 = l_Lean_instInhabitedSourceInfo___closed__1;
x_29 = l_Lean_Syntax_mkLit(x_27, x_26, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_13);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_11);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_12);
if (x_35 == 0)
{
return x_12;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_12, 0);
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_12);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
static lean_object* _init_l_Lean_termEvalPrec_x21_____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("termEvalPrec!_");
return x_1;
}
}
static lean_object* _init_l_Lean_termEvalPrec_x21_____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__2;
x_2 = l_Lean_termEvalPrec_x21_____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_termEvalPrec_x21_____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalPrec! ");
return x_1;
}
}
static lean_object* _init_l_Lean_termEvalPrec_x21_____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_termEvalPrec_x21_____closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_termEvalPrec_x21_____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__14;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_termEvalPrec_x21_____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__10;
x_2 = l_Lean_termEvalPrec_x21_____closed__4;
x_3 = l_Lean_termEvalPrec_x21_____closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_termEvalPrec_x21_____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_termEvalPrec_x21_____closed__2;
x_2 = lean_unsigned_to_nat(1023u);
x_3 = l_Lean_termEvalPrec_x21_____closed__6;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_termEvalPrec_x21__() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_termEvalPrec_x21_____closed__7;
return x_1;
}
}
lean_object* l_Lean_myMacro____x40_Init_Meta___hyg_4159_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_termEvalPrec_x21_____closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l_Lean_evalPrec(x_9, x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Nat_repr(x_12);
x_14 = l_Lean_numLitKind;
x_15 = l_Lean_instInhabitedSourceInfo___closed__1;
x_16 = l_Lean_Syntax_mkLit(x_14, x_13, x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = l_Nat_repr(x_17);
x_20 = l_Lean_numLitKind;
x_21 = l_Lean_instInhabitedSourceInfo___closed__1;
x_22 = l_Lean_Syntax_mkLit(x_20, x_19, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
return x_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
lean_object* l_Lean_evalOptPrec_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_evalOptPrec_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_evalOptPrec_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_evalOptPrec(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_evalPrec(x_6, x_2, x_3);
return x_7;
}
}
}
static lean_object* _init_l_Lean_evalPrio___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected priority");
return x_1;
}
}
lean_object* l_Lean_evalPrio(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get(x_2, 4);
x_10 = lean_ctor_get(x_2, 5);
x_11 = lean_nat_dec_eq(x_8, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_8, x_12);
lean_dec(x_8);
lean_ctor_set(x_2, 3, x_13);
lean_inc(x_2);
x_14 = l_Lean_expandMacros(x_1, x_2, x_3);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_numLitKind___closed__2;
lean_inc(x_16);
x_19 = l_Lean_Syntax_isOfKind(x_16, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_14);
x_20 = l_Lean_evalPrio___closed__1;
x_21 = l_Lean_Macro_throwErrorAt___rarg(x_16, x_20, x_2, x_17);
lean_dec(x_16);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_22 = l_Lean_numLitKind;
x_23 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_22, x_16);
lean_dec(x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = l_Lean_numLitKind___closed__2;
lean_inc(x_26);
x_29 = l_Lean_Syntax_isOfKind(x_26, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_evalPrio___closed__1;
x_31 = l_Lean_Macro_throwErrorAt___rarg(x_26, x_30, x_2, x_27);
lean_dec(x_26);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_2);
x_32 = l_Lean_numLitKind;
x_33 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_32, x_26);
lean_dec(x_26);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_14);
if (x_38 == 0)
{
return x_14;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_14, 0);
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_14);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_free_object(x_2);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_42 = l_Lean_maxRecDepthErrorMessage;
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_3);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
x_47 = lean_ctor_get(x_2, 2);
x_48 = lean_ctor_get(x_2, 3);
x_49 = lean_ctor_get(x_2, 4);
x_50 = lean_ctor_get(x_2, 5);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_2);
x_51 = lean_nat_dec_eq(x_48, x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_48, x_52);
lean_dec(x_48);
x_54 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_46);
lean_ctor_set(x_54, 2, x_47);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set(x_54, 4, x_49);
lean_ctor_set(x_54, 5, x_50);
lean_inc(x_54);
x_55 = l_Lean_expandMacros(x_1, x_54, x_3);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
x_59 = l_Lean_numLitKind___closed__2;
lean_inc(x_56);
x_60 = l_Lean_Syntax_isOfKind(x_56, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_58);
x_61 = l_Lean_evalPrio___closed__1;
x_62 = l_Lean_Macro_throwErrorAt___rarg(x_56, x_61, x_54, x_57);
lean_dec(x_56);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_54);
x_63 = l_Lean_numLitKind;
x_64 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_63, x_56);
lean_dec(x_56);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_58)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_58;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_57);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
lean_dec(x_64);
if (lean_is_scalar(x_58)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_58;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_57);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_54);
x_69 = lean_ctor_get(x_55, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_55, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_71 = x_55;
} else {
 lean_dec_ref(x_55);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
x_73 = l_Lean_maxRecDepthErrorMessage;
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_3);
return x_75;
}
}
}
}
lean_object* l_Lean_myMacro____x40_Init_Meta___hyg_4290_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Syntax_addPrio___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
lean_inc(x_2);
x_12 = l_Lean_evalPrio(x_9, x_2, x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_evalPrio(x_11, x_2, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_17);
lean_dec(x_13);
x_19 = l_Nat_repr(x_18);
x_20 = l_Lean_numLitKind;
x_21 = l_Lean_instInhabitedSourceInfo___closed__1;
x_22 = l_Lean_Syntax_mkLit(x_20, x_19, x_21);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_nat_add(x_13, x_23);
lean_dec(x_23);
lean_dec(x_13);
x_26 = l_Nat_repr(x_25);
x_27 = l_Lean_numLitKind;
x_28 = l_Lean_instInhabitedSourceInfo___closed__1;
x_29 = l_Lean_Syntax_mkLit(x_27, x_26, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_13);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_11);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_12);
if (x_35 == 0)
{
return x_12;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_12, 0);
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_12);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
lean_object* l_Lean_myMacro____x40_Init_Meta___hyg_4388_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Syntax_subPrio___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
lean_inc(x_2);
x_12 = l_Lean_evalPrio(x_9, x_2, x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_evalPrio(x_11, x_2, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_nat_sub(x_13, x_17);
lean_dec(x_17);
lean_dec(x_13);
x_19 = l_Nat_repr(x_18);
x_20 = l_Lean_numLitKind;
x_21 = l_Lean_instInhabitedSourceInfo___closed__1;
x_22 = l_Lean_Syntax_mkLit(x_20, x_19, x_21);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_nat_sub(x_13, x_23);
lean_dec(x_23);
lean_dec(x_13);
x_26 = l_Nat_repr(x_25);
x_27 = l_Lean_numLitKind;
x_28 = l_Lean_instInhabitedSourceInfo___closed__1;
x_29 = l_Lean_Syntax_mkLit(x_27, x_26, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_13);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_11);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_12);
if (x_35 == 0)
{
return x_12;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_12, 0);
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_12);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
static lean_object* _init_l_Lean_termEvalPrio_x21_____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("termEvalPrio!_");
return x_1;
}
}
static lean_object* _init_l_Lean_termEvalPrio_x21_____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__2;
x_2 = l_Lean_termEvalPrio_x21_____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_termEvalPrio_x21_____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalPrio! ");
return x_1;
}
}
static lean_object* _init_l_Lean_termEvalPrio_x21_____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_termEvalPrio_x21_____closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_termEvalPrio_x21_____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrio___closed__4;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_termEvalPrio_x21_____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__10;
x_2 = l_Lean_termEvalPrio_x21_____closed__4;
x_3 = l_Lean_termEvalPrio_x21_____closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_termEvalPrio_x21_____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_termEvalPrio_x21_____closed__2;
x_2 = lean_unsigned_to_nat(1023u);
x_3 = l_Lean_termEvalPrio_x21_____closed__6;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_termEvalPrio_x21__() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_termEvalPrio_x21_____closed__7;
return x_1;
}
}
lean_object* l_Lean_myMacro____x40_Init_Meta___hyg_4507_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_termEvalPrio_x21_____closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l_Lean_evalPrio(x_9, x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Nat_repr(x_12);
x_14 = l_Lean_numLitKind;
x_15 = l_Lean_instInhabitedSourceInfo___closed__1;
x_16 = l_Lean_Syntax_mkLit(x_14, x_13, x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = l_Nat_repr(x_17);
x_20 = l_Lean_numLitKind;
x_21 = l_Lean_instInhabitedSourceInfo___closed__1;
x_22 = l_Lean_Syntax_mkLit(x_20, x_19, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
return x_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
lean_object* l_Lean_evalOptPrio_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_evalOptPrio_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_evalOptPrio_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_evalOptPrio(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_unsigned_to_nat(1000u);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_evalPrio(x_6, x_2, x_3);
return x_7;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Array_getSepElems___spec__1___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = x_2 + x_7;
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 0);
lean_dec(x_12);
x_13 = 1;
x_14 = lean_box(x_13);
lean_ctor_set(x_4, 0, x_14);
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = 1;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
x_2 = x_8;
x_4 = x_19;
goto _start;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = lean_array_push(x_22, x_6);
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set(x_4, 1, x_24);
lean_ctor_set(x_4, 0, x_26);
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_dec(x_4);
x_29 = lean_array_push(x_28, x_6);
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
x_2 = x_8;
x_4 = x_32;
goto _start;
}
}
}
else
{
return x_4;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Array_getSepElems___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_getSepElems___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_getSepElems___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Array_empty___closed__1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l_Array_empty___closed__1;
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Array_getEvenElems___rarg___closed__1;
x_11 = l_Array_foldlMUnsafe_fold___at_Array_getSepElems___spec__1___rarg(x_1, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
return x_12;
}
}
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
lean_object* l_Array_foldlMUnsafe_fold___at_Array_getSepElems___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Array_getSepElems___spec__1___rarg(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
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
lean_object* l___private_Init_Meta_0__Array_filterSepElemsMAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_add(x_1, x_8);
lean_dec(x_1);
x_10 = l___private_Init_Meta_0__Array_filterSepElemsMAux___rarg(x_2, x_3, x_4, x_9, x_5);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = l_Array_isEmpty___rarg(x_5);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_1, x_12);
x_14 = l_instDecidableNot___rarg(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_add(x_1, x_15);
lean_dec(x_1);
x_17 = lean_array_push(x_5, x_6);
x_18 = l___private_Init_Meta_0__Array_filterSepElemsMAux___rarg(x_2, x_3, x_4, x_16, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_1);
x_19 = lean_nat_sub(x_1, lean_box(1));
x_20 = lean_array_fget(x_3, x_19);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_add(x_1, x_21);
lean_dec(x_1);
x_23 = lean_array_push(x_5, x_20);
x_24 = lean_array_push(x_23, x_6);
x_25 = l___private_Init_Meta_0__Array_filterSepElemsMAux___rarg(x_2, x_3, x_4, x_22, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_nat_add(x_1, x_26);
lean_dec(x_1);
x_28 = lean_array_push(x_5, x_6);
x_29 = l___private_Init_Meta_0__Array_filterSepElemsMAux___rarg(x_2, x_3, x_4, x_27, x_28);
return x_29;
}
}
}
}
lean_object* l___private_Init_Meta_0__Array_filterSepElemsMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_fget(x_2, x_4);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_3);
lean_inc(x_11);
x_13 = lean_apply_1(x_3, x_11);
x_14 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Array_filterSepElemsMAux___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_3);
lean_closure_set(x_14, 4, x_5);
lean_closure_set(x_14, 5, x_11);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
lean_object* l___private_Init_Meta_0__Array_filterSepElemsMAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Array_filterSepElemsMAux___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_Meta_0__Array_filterSepElemsMAux___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l___private_Init_Meta_0__Array_filterSepElemsMAux___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
lean_object* l_Array_filterSepElemsM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_empty___closed__1;
x_6 = l___private_Init_Meta_0__Array_filterSepElemsMAux___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_filterSepElemsM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_filterSepElemsM___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Meta_0__Array_filterSepElemsMAux___at_Array_filterSepElems___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_1, x_3);
lean_inc(x_2);
lean_inc(x_7);
x_8 = lean_apply_1(x_2, x_7);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = l_Array_isEmpty___rarg(x_4);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
x_16 = l_instDecidableNot___rarg(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_add(x_3, x_17);
lean_dec(x_3);
x_19 = lean_array_push(x_4, x_7);
x_3 = x_18;
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc(x_3);
x_21 = lean_nat_sub(x_3, lean_box(1));
x_22 = lean_array_fget(x_1, x_21);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_nat_add(x_3, x_23);
lean_dec(x_3);
x_25 = lean_array_push(x_4, x_22);
x_26 = lean_array_push(x_25, x_7);
x_3 = x_24;
x_4 = x_26;
goto _start;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_nat_add(x_3, x_28);
lean_dec(x_3);
x_30 = lean_array_push(x_4, x_7);
x_3 = x_29;
x_4 = x_30;
goto _start;
}
}
}
}
}
lean_object* l_Array_filterSepElemsM___at_Array_filterSepElems___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_empty___closed__1;
x_5 = l___private_Init_Meta_0__Array_filterSepElemsMAux___at_Array_filterSepElems___spec__2(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_filterSepElems(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_filterSepElemsM___at_Array_filterSepElems___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Meta_0__Array_filterSepElemsMAux___at_Array_filterSepElems___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Meta_0__Array_filterSepElemsMAux___at_Array_filterSepElems___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_filterSepElemsM___at_Array_filterSepElems___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_filterSepElemsM___at_Array_filterSepElems___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_filterSepElems___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_filterSepElems(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = lean_array_push(x_2, x_6);
x_10 = l___private_Init_Meta_0__Array_mapSepElemsMAux___rarg(x_3, x_4, x_5, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_array_fget(x_2, x_4);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_mod(x_4, x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
x_18 = lean_array_push(x_5, x_11);
x_4 = x_17;
x_5 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_3);
x_21 = lean_apply_1(x_3, x_11);
x_22 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Array_mapSepElemsMAux___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_22, 0, x_4);
lean_closure_set(x_22, 1, x_5);
lean_closure_set(x_22, 2, x_1);
lean_closure_set(x_22, 3, x_2);
lean_closure_set(x_22, 4, x_3);
x_23 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_21, x_22);
return x_23;
}
}
}
}
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Array_mapSepElemsMAux___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Meta_0__Array_mapSepElemsMAux___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapSepElemsM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_empty___closed__1;
x_6 = l___private_Init_Meta_0__Array_mapSepElemsMAux___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_mapSepElemsM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapSepElemsM___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Array_mapSepElems___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_mod(x_3, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_14 = lean_array_push(x_4, x_7);
x_3 = x_13;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_2);
x_16 = lean_apply_1(x_2, x_7);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_3, x_17);
lean_dec(x_3);
x_19 = lean_array_push(x_4, x_16);
x_3 = x_18;
x_4 = x_19;
goto _start;
}
}
}
}
lean_object* l_Array_mapSepElemsM___at_Array_mapSepElems___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_empty___closed__1;
x_5 = l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Array_mapSepElems___spec__2(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_mapSepElems(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mapSepElemsM___at_Array_mapSepElems___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Array_mapSepElems___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Array_mapSepElems___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_mapSepElemsM___at_Array_mapSepElems___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mapSepElemsM___at_Array_mapSepElems___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_mapSepElems___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mapSepElems(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = x_2 + x_7;
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 0);
lean_dec(x_12);
x_13 = 1;
x_14 = lean_box(x_13);
lean_ctor_set(x_4, 0, x_14);
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = 1;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
x_2 = x_8;
x_4 = x_19;
goto _start;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = lean_array_push(x_22, x_6);
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set(x_4, 1, x_24);
lean_ctor_set(x_4, 0, x_26);
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_dec(x_4);
x_29 = lean_array_push(x_28, x_6);
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
x_2 = x_8;
x_4 = x_32;
goto _start;
}
}
}
else
{
return x_4;
}
}
}
lean_object* l_Lean_Syntax_SepArray_getElems___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Array_empty___closed__1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l_Array_empty___closed__1;
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Array_getEvenElems___rarg___closed__1;
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_1, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_Syntax_SepArray_getElems(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_getElems___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Syntax_SepArray_getElems___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_SepArray_getElems___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_SepArray_getElems(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_SepArray_instCoeSepArrayArraySyntax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_getElems___rarg___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Syntax_SepArray_instCoeSepArrayArraySyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_SepArray_instCoeSepArrayArraySyntax___closed__1;
return x_2;
}
}
lean_object* l_Lean_Syntax_SepArray_instCoeSepArrayArraySyntax___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_SepArray_instCoeSepArrayArraySyntax(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrQuotedChar_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrQuotedChar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrQuotedChar_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 123;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_decodeQuotedChar(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint32_t x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_4 = lean_string_utf8_get(x_1, x_2);
x_5 = lean_string_utf8_next(x_1, x_2);
x_6 = 123;
x_7 = x_4 == x_6;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrQuotedChar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrLit_loop_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrLit_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrLit_loop_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = 123;
x_9 = x_4 == x_8;
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_string_utf8_at_end(x_1, x_5);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 92;
x_12 = x_4 == x_11;
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_string_push(x_3, x_4);
x_2 = x_5;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrQuotedChar(x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unbox_uint32(x_18);
lean_dec(x_18);
x_21 = lean_string_push(x_3, x_20);
x_2 = x_19;
x_3 = x_21;
goto _start;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_5);
lean_dec(x_3);
x_23 = lean_box(0);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_3);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_5);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_3);
return x_25;
}
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrLit_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrLit_loop(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_instInhabitedParserDescr___closed__1;
x_4 = l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrLit_loop(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrLit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrLit(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isInterpolatedStrLit_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_interpolatedStrLitKind;
x_3 = l_Lean_Syntax_isLit_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_instInhabitedParserDescr___closed__1;
x_8 = l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrLit_loop(x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
}
lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isInterpolatedStrLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_expandInterpolatedStrChunks_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_expandInterpolatedStrChunks_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_expandInterpolatedStrChunks_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_5);
x_10 = lean_apply_4(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_apply_5(x_7, x_2, x_11, x_13, x_5, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_5);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_apply_5(x_7, x_2, x_4, x_19, x_5, x_6);
return x_20;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_5 < x_4;
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_uget(x_3, x_5);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = l_Lean_Syntax_isInterpolatedStrLit_x3f(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_inc(x_2);
lean_inc(x_7);
x_15 = lean_apply_3(x_2, x_11, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_7);
lean_inc(x_1);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2(x_1, x_12, x_13, x_16, x_7, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = 1;
x_29 = x_5 + x_28;
x_5 = x_29;
x_6 = x_27;
x_8 = x_26;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_15);
if (x_35 == 0)
{
return x_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_15, 0);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_15);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_11);
x_39 = lean_ctor_get(x_14, 0);
lean_inc(x_39);
lean_dec(x_14);
x_40 = l_Lean_instInhabitedSourceInfo___closed__1;
x_41 = l_Lean_Syntax_mkStrLit(x_39, x_40);
lean_dec(x_39);
lean_inc(x_2);
lean_inc(x_7);
x_42 = lean_apply_3(x_2, x_41, x_7, x_8);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_7);
lean_inc(x_1);
x_45 = l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2(x_1, x_12, x_13, x_43, x_7, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
lean_dec(x_46);
lean_ctor_set(x_45, 0, x_49);
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; 
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_dec(x_45);
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
lean_dec(x_46);
x_55 = 1;
x_56 = x_5 + x_55;
x_5 = x_56;
x_6 = x_54;
x_8 = x_53;
goto _start;
}
}
else
{
uint8_t x_58; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
return x_45;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_45);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_42);
if (x_62 == 0)
{
return x_42;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_42, 0);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_42);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Syntax_expandInterpolatedStrChunks___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Lean_Syntax_expandInterpolatedStrChunks___closed__1;
x_10 = l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1(x_2, x_3, x_1, x_7, x_8, x_9, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_expandInterpolatedStrChunks(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Syntax_expandInterpolatedStr___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("++");
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_expandInterpolatedStr___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedSourceInfo___closed__1;
x_2 = l_Lean_Syntax_expandInterpolatedStr___lambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_Array_empty___closed__1;
x_6 = lean_array_push(x_5, x_1);
x_7 = l_Lean_Syntax_expandInterpolatedStr___lambda__1___closed__2;
x_8 = lean_array_push(x_6, x_7);
x_9 = lean_array_push(x_8, x_2);
x_10 = l_term___x2b_x2b_____closed__2;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStr___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l_Array_empty___closed__1;
x_6 = lean_array_push(x_5, x_1);
x_7 = lean_array_push(x_5, x_2);
x_8 = l_Lean_nullKind___closed__2;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_array_push(x_6, x_9);
x_11 = l_myMacro____x40_Init_Notation___hyg_2094____closed__4;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
static lean_object* _init_l_Lean_Syntax_expandInterpolatedStr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_expandInterpolatedStr___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Syntax_getArgs(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Syntax_expandInterpolatedStr___lambda__2___boxed), 4, 1);
lean_closure_set(x_7, 0, x_3);
x_8 = l_Lean_Syntax_expandInterpolatedStr___closed__1;
x_9 = l_Lean_Syntax_expandInterpolatedStrChunks(x_6, x_8, x_7, x_4, x_5);
lean_dec(x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Array_empty___closed__1;
x_13 = lean_array_push(x_12, x_11);
x_14 = l_myMacro____x40_Init_Notation___hyg_12721____closed__11;
x_15 = lean_array_push(x_14, x_2);
x_16 = l_myMacro____x40_Init_Notation___hyg_12721____closed__8;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_array_push(x_12, x_17);
x_19 = l_Lean_nullKind___closed__2;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_array_push(x_13, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_myMacro____x40_Init_Notation___hyg_11259____closed__9;
x_24 = lean_array_push(x_23, x_22);
x_25 = l_myMacro____x40_Init_Notation___hyg_730____closed__8;
x_26 = lean_array_push(x_24, x_25);
x_27 = l_myMacro____x40_Init_Notation___hyg_11259____closed__8;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_9, 0, x_28);
return x_9;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = l_Array_empty___closed__1;
x_32 = lean_array_push(x_31, x_29);
x_33 = l_myMacro____x40_Init_Notation___hyg_12721____closed__11;
x_34 = lean_array_push(x_33, x_2);
x_35 = l_myMacro____x40_Init_Notation___hyg_12721____closed__8;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_array_push(x_31, x_36);
x_38 = l_Lean_nullKind___closed__2;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_array_push(x_32, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_myMacro____x40_Init_Notation___hyg_11259____closed__9;
x_43 = lean_array_push(x_42, x_41);
x_44 = l_myMacro____x40_Init_Notation___hyg_730____closed__8;
x_45 = lean_array_push(x_43, x_44);
x_46 = l_myMacro____x40_Init_Notation___hyg_11259____closed__8;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_30);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_9);
if (x_49 == 0)
{
return x_9;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_9, 0);
x_51 = lean_ctor_get(x_9, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_9);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_expandInterpolatedStr___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStr___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_expandInterpolatedStr___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_expandInterpolatedStr(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Syntax_getSepArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_Lean_Syntax_getArgs(x_1);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Array_empty___closed__1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Array_empty___closed__1;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_getEvenElems___rarg___closed__1;
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_2, x_9, x_10, x_11);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getSepArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Array_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Meta(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_idBeginEscape = _init_l_Lean_idBeginEscape();
l_Lean_idEndEscape = _init_l_Lean_idEndEscape();
l_Lean_Name_toStringWithSep___closed__1 = _init_l_Lean_Name_toStringWithSep___closed__1();
lean_mark_persistent(l_Lean_Name_toStringWithSep___closed__1);
l_Lean_Name_toString___closed__1 = _init_l_Lean_Name_toString___closed__1();
lean_mark_persistent(l_Lean_Name_toString___closed__1);
l_Lean_Name_instToStringName___closed__1 = _init_l_Lean_Name_instToStringName___closed__1();
lean_mark_persistent(l_Lean_Name_instToStringName___closed__1);
l_Lean_Name_instToStringName = _init_l_Lean_Name_instToStringName();
lean_mark_persistent(l_Lean_Name_instToStringName);
l_Lean_Name_instReprName___closed__1 = _init_l_Lean_Name_instReprName___closed__1();
lean_mark_persistent(l_Lean_Name_instReprName___closed__1);
l_Lean_Name_instReprName___closed__2 = _init_l_Lean_Name_instReprName___closed__2();
lean_mark_persistent(l_Lean_Name_instReprName___closed__2);
l_Lean_NameGenerator_namePrefix___default___closed__1 = _init_l_Lean_NameGenerator_namePrefix___default___closed__1();
lean_mark_persistent(l_Lean_NameGenerator_namePrefix___default___closed__1);
l_Lean_NameGenerator_namePrefix___default___closed__2 = _init_l_Lean_NameGenerator_namePrefix___default___closed__2();
lean_mark_persistent(l_Lean_NameGenerator_namePrefix___default___closed__2);
l_Lean_NameGenerator_namePrefix___default = _init_l_Lean_NameGenerator_namePrefix___default();
lean_mark_persistent(l_Lean_NameGenerator_namePrefix___default);
l_Lean_NameGenerator_idx___default = _init_l_Lean_NameGenerator_idx___default();
lean_mark_persistent(l_Lean_NameGenerator_idx___default);
l_Lean_instInhabitedNameGenerator___closed__1 = _init_l_Lean_instInhabitedNameGenerator___closed__1();
lean_mark_persistent(l_Lean_instInhabitedNameGenerator___closed__1);
l_Lean_instInhabitedNameGenerator = _init_l_Lean_instInhabitedNameGenerator();
lean_mark_persistent(l_Lean_instInhabitedNameGenerator);
l_Lean_expandMacros___boxed__const__1 = _init_l_Lean_expandMacros___boxed__const__1();
lean_mark_persistent(l_Lean_expandMacros___boxed__const__1);
l_Lean_mkCIdentFrom___closed__1 = _init_l_Lean_mkCIdentFrom___closed__1();
lean_mark_persistent(l_Lean_mkCIdentFrom___closed__1);
l_Lean_mkCIdentFrom___closed__2 = _init_l_Lean_mkCIdentFrom___closed__2();
lean_mark_persistent(l_Lean_mkCIdentFrom___closed__2);
l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___closed__1);
l_Lean_mkSepArray___closed__1 = _init_l_Lean_mkSepArray___closed__1();
lean_mark_persistent(l_Lean_mkSepArray___closed__1);
l_Lean_mkOptionalNode___closed__1 = _init_l_Lean_mkOptionalNode___closed__1();
lean_mark_persistent(l_Lean_mkOptionalNode___closed__1);
l_Lean_mkOptionalNode___closed__2 = _init_l_Lean_mkOptionalNode___closed__2();
lean_mark_persistent(l_Lean_mkOptionalNode___closed__2);
l_Lean_Syntax_mkApp___closed__1 = _init_l_Lean_Syntax_mkApp___closed__1();
lean_mark_persistent(l_Lean_Syntax_mkApp___closed__1);
l_Lean_Syntax_decodeNatLitVal_x3f___closed__1 = _init_l_Lean_Syntax_decodeNatLitVal_x3f___closed__1();
lean_mark_persistent(l_Lean_Syntax_decodeNatLitVal_x3f___closed__1);
l_Lean_Syntax_decodeQuotedChar___boxed__const__1 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__1);
l_Lean_Syntax_decodeQuotedChar___boxed__const__2 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__2);
l_Lean_Syntax_decodeQuotedChar___boxed__const__3 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__3);
l_Lean_Syntax_decodeQuotedChar___boxed__const__4 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__4);
l_Lean_Syntax_decodeQuotedChar___boxed__const__5 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__5);
l_Lean_Syntax_decodeQuotedChar___boxed__const__6 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__6);
l_Lean_Syntax_strLitToAtom___closed__1 = _init_l_Lean_Syntax_strLitToAtom___closed__1();
lean_mark_persistent(l_Lean_Syntax_strLitToAtom___closed__1);
l_Lean_Syntax_strLitToAtom___closed__2 = _init_l_Lean_Syntax_strLitToAtom___closed__2();
lean_mark_persistent(l_Lean_Syntax_strLitToAtom___closed__2);
l_Lean_Syntax_strLitToAtom___closed__3 = _init_l_Lean_Syntax_strLitToAtom___closed__3();
lean_mark_persistent(l_Lean_Syntax_strLitToAtom___closed__3);
l_Lean_Syntax_strLitToAtom___closed__4 = _init_l_Lean_Syntax_strLitToAtom___closed__4();
lean_mark_persistent(l_Lean_Syntax_strLitToAtom___closed__4);
l_Lean_instQuoteSyntax = _init_l_Lean_instQuoteSyntax();
lean_mark_persistent(l_Lean_instQuoteSyntax);
l_Lean_instQuoteBool___closed__1 = _init_l_Lean_instQuoteBool___closed__1();
lean_mark_persistent(l_Lean_instQuoteBool___closed__1);
l_Lean_instQuoteBool___closed__2 = _init_l_Lean_instQuoteBool___closed__2();
lean_mark_persistent(l_Lean_instQuoteBool___closed__2);
l_Lean_instQuoteBool___closed__3 = _init_l_Lean_instQuoteBool___closed__3();
lean_mark_persistent(l_Lean_instQuoteBool___closed__3);
l_Lean_instQuoteBool___closed__4 = _init_l_Lean_instQuoteBool___closed__4();
lean_mark_persistent(l_Lean_instQuoteBool___closed__4);
l_Lean_instQuoteBool___closed__5 = _init_l_Lean_instQuoteBool___closed__5();
lean_mark_persistent(l_Lean_instQuoteBool___closed__5);
l_Lean_instQuoteBool___closed__6 = _init_l_Lean_instQuoteBool___closed__6();
lean_mark_persistent(l_Lean_instQuoteBool___closed__6);
l_Lean_instQuoteSubstring___closed__1 = _init_l_Lean_instQuoteSubstring___closed__1();
lean_mark_persistent(l_Lean_instQuoteSubstring___closed__1);
l_Lean_instQuoteSubstring___closed__2 = _init_l_Lean_instQuoteSubstring___closed__2();
lean_mark_persistent(l_Lean_instQuoteSubstring___closed__2);
l_Lean_instQuoteSubstring___closed__3 = _init_l_Lean_instQuoteSubstring___closed__3();
lean_mark_persistent(l_Lean_instQuoteSubstring___closed__3);
l_Lean_instQuoteSubstring___closed__4 = _init_l_Lean_instQuoteSubstring___closed__4();
lean_mark_persistent(l_Lean_instQuoteSubstring___closed__4);
l___private_Init_Meta_0__Lean_quoteName___closed__1 = _init_l___private_Init_Meta_0__Lean_quoteName___closed__1();
lean_mark_persistent(l___private_Init_Meta_0__Lean_quoteName___closed__1);
l___private_Init_Meta_0__Lean_quoteName___closed__2 = _init_l___private_Init_Meta_0__Lean_quoteName___closed__2();
lean_mark_persistent(l___private_Init_Meta_0__Lean_quoteName___closed__2);
l___private_Init_Meta_0__Lean_quoteName___closed__3 = _init_l___private_Init_Meta_0__Lean_quoteName___closed__3();
lean_mark_persistent(l___private_Init_Meta_0__Lean_quoteName___closed__3);
l___private_Init_Meta_0__Lean_quoteName___closed__4 = _init_l___private_Init_Meta_0__Lean_quoteName___closed__4();
lean_mark_persistent(l___private_Init_Meta_0__Lean_quoteName___closed__4);
l___private_Init_Meta_0__Lean_quoteName___closed__5 = _init_l___private_Init_Meta_0__Lean_quoteName___closed__5();
lean_mark_persistent(l___private_Init_Meta_0__Lean_quoteName___closed__5);
l___private_Init_Meta_0__Lean_quoteName___closed__6 = _init_l___private_Init_Meta_0__Lean_quoteName___closed__6();
lean_mark_persistent(l___private_Init_Meta_0__Lean_quoteName___closed__6);
l___private_Init_Meta_0__Lean_quoteName___closed__7 = _init_l___private_Init_Meta_0__Lean_quoteName___closed__7();
lean_mark_persistent(l___private_Init_Meta_0__Lean_quoteName___closed__7);
l___private_Init_Meta_0__Lean_quoteName___closed__8 = _init_l___private_Init_Meta_0__Lean_quoteName___closed__8();
lean_mark_persistent(l___private_Init_Meta_0__Lean_quoteName___closed__8);
l___private_Init_Meta_0__Lean_quoteName___closed__9 = _init_l___private_Init_Meta_0__Lean_quoteName___closed__9();
lean_mark_persistent(l___private_Init_Meta_0__Lean_quoteName___closed__9);
l_Lean_instQuoteName___closed__1 = _init_l_Lean_instQuoteName___closed__1();
lean_mark_persistent(l_Lean_instQuoteName___closed__1);
l_Lean_instQuoteName = _init_l_Lean_instQuoteName();
lean_mark_persistent(l_Lean_instQuoteName);
l_Lean_instQuoteProd___rarg___closed__1 = _init_l_Lean_instQuoteProd___rarg___closed__1();
lean_mark_persistent(l_Lean_instQuoteProd___rarg___closed__1);
l_Lean_instQuoteProd___rarg___closed__2 = _init_l_Lean_instQuoteProd___rarg___closed__2();
lean_mark_persistent(l_Lean_instQuoteProd___rarg___closed__2);
l___private_Init_Meta_0__Lean_quoteList___rarg___closed__1 = _init_l___private_Init_Meta_0__Lean_quoteList___rarg___closed__1();
lean_mark_persistent(l___private_Init_Meta_0__Lean_quoteList___rarg___closed__1);
l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__1 = _init_l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__1();
lean_mark_persistent(l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__1);
l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__2 = _init_l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__2();
lean_mark_persistent(l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__2);
l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__3 = _init_l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__3();
lean_mark_persistent(l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__3);
l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__4 = _init_l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__4();
lean_mark_persistent(l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__4);
l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__5 = _init_l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__5();
lean_mark_persistent(l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__5);
l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__6 = _init_l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__6();
lean_mark_persistent(l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__6);
l_Lean_evalPrec___closed__1 = _init_l_Lean_evalPrec___closed__1();
lean_mark_persistent(l_Lean_evalPrec___closed__1);
l_Lean_termEvalPrec_x21_____closed__1 = _init_l_Lean_termEvalPrec_x21_____closed__1();
lean_mark_persistent(l_Lean_termEvalPrec_x21_____closed__1);
l_Lean_termEvalPrec_x21_____closed__2 = _init_l_Lean_termEvalPrec_x21_____closed__2();
lean_mark_persistent(l_Lean_termEvalPrec_x21_____closed__2);
l_Lean_termEvalPrec_x21_____closed__3 = _init_l_Lean_termEvalPrec_x21_____closed__3();
lean_mark_persistent(l_Lean_termEvalPrec_x21_____closed__3);
l_Lean_termEvalPrec_x21_____closed__4 = _init_l_Lean_termEvalPrec_x21_____closed__4();
lean_mark_persistent(l_Lean_termEvalPrec_x21_____closed__4);
l_Lean_termEvalPrec_x21_____closed__5 = _init_l_Lean_termEvalPrec_x21_____closed__5();
lean_mark_persistent(l_Lean_termEvalPrec_x21_____closed__5);
l_Lean_termEvalPrec_x21_____closed__6 = _init_l_Lean_termEvalPrec_x21_____closed__6();
lean_mark_persistent(l_Lean_termEvalPrec_x21_____closed__6);
l_Lean_termEvalPrec_x21_____closed__7 = _init_l_Lean_termEvalPrec_x21_____closed__7();
lean_mark_persistent(l_Lean_termEvalPrec_x21_____closed__7);
l_Lean_termEvalPrec_x21__ = _init_l_Lean_termEvalPrec_x21__();
lean_mark_persistent(l_Lean_termEvalPrec_x21__);
l_Lean_evalPrio___closed__1 = _init_l_Lean_evalPrio___closed__1();
lean_mark_persistent(l_Lean_evalPrio___closed__1);
l_Lean_termEvalPrio_x21_____closed__1 = _init_l_Lean_termEvalPrio_x21_____closed__1();
lean_mark_persistent(l_Lean_termEvalPrio_x21_____closed__1);
l_Lean_termEvalPrio_x21_____closed__2 = _init_l_Lean_termEvalPrio_x21_____closed__2();
lean_mark_persistent(l_Lean_termEvalPrio_x21_____closed__2);
l_Lean_termEvalPrio_x21_____closed__3 = _init_l_Lean_termEvalPrio_x21_____closed__3();
lean_mark_persistent(l_Lean_termEvalPrio_x21_____closed__3);
l_Lean_termEvalPrio_x21_____closed__4 = _init_l_Lean_termEvalPrio_x21_____closed__4();
lean_mark_persistent(l_Lean_termEvalPrio_x21_____closed__4);
l_Lean_termEvalPrio_x21_____closed__5 = _init_l_Lean_termEvalPrio_x21_____closed__5();
lean_mark_persistent(l_Lean_termEvalPrio_x21_____closed__5);
l_Lean_termEvalPrio_x21_____closed__6 = _init_l_Lean_termEvalPrio_x21_____closed__6();
lean_mark_persistent(l_Lean_termEvalPrio_x21_____closed__6);
l_Lean_termEvalPrio_x21_____closed__7 = _init_l_Lean_termEvalPrio_x21_____closed__7();
lean_mark_persistent(l_Lean_termEvalPrio_x21_____closed__7);
l_Lean_termEvalPrio_x21__ = _init_l_Lean_termEvalPrio_x21__();
lean_mark_persistent(l_Lean_termEvalPrio_x21__);
l_Lean_Syntax_SepArray_instCoeSepArrayArraySyntax___closed__1 = _init_l_Lean_Syntax_SepArray_instCoeSepArrayArraySyntax___closed__1();
lean_mark_persistent(l_Lean_Syntax_SepArray_instCoeSepArrayArraySyntax___closed__1);
l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1 = _init_l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1();
lean_mark_persistent(l___private_Init_Meta_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1);
l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2___closed__1);
l_Lean_Syntax_expandInterpolatedStrChunks___closed__1 = _init_l_Lean_Syntax_expandInterpolatedStrChunks___closed__1();
lean_mark_persistent(l_Lean_Syntax_expandInterpolatedStrChunks___closed__1);
l_Lean_Syntax_expandInterpolatedStr___lambda__1___closed__1 = _init_l_Lean_Syntax_expandInterpolatedStr___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Syntax_expandInterpolatedStr___lambda__1___closed__1);
l_Lean_Syntax_expandInterpolatedStr___lambda__1___closed__2 = _init_l_Lean_Syntax_expandInterpolatedStr___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Syntax_expandInterpolatedStr___lambda__1___closed__2);
l_Lean_Syntax_expandInterpolatedStr___closed__1 = _init_l_Lean_Syntax_expandInterpolatedStr___closed__1();
lean_mark_persistent(l_Lean_Syntax_expandInterpolatedStr___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
