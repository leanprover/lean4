// Lean compiler output
// Module: Init.LeanInit
// Imports: Init.Data.String.Basic Init.Data.Array.Basic Init.Data.UInt Init.Data.Hashable Init.Control.Reader Init.Control.Except
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
lean_object* l_Array_findSomeMAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_1__eraseMacroScopesAux___main___closed__1;
lean_object* l_Lean_MacroM_monadQuotation;
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___closed__1;
lean_object* l_Array_mapSepElemsM___boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__1;
lean_object* l_Lean_MacroScopesView_inhabited;
lean_object* l___private_Init_LeanInit_10__decodeDecimalLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkTermIdFromIdent(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_nullKind;
lean_object* l_Lean_Name_HasAppend;
lean_object* l___private_Init_LeanInit_2__assembleParts___main(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_identToAtom___boxed(lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___boxed(lean_object*, lean_object*);
lean_object* l_Lean_identKind___closed__1;
lean_object* l_Lean_fieldIdxKind___closed__2;
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_ParserDescr_orelse(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MacroM_monadQuotation___lambda__2(lean_object*);
lean_object* l___private_Init_LeanInit_8__decodeHexDigit___boxed(lean_object*, lean_object*);
uint32_t l_Lean_idBeginEscape;
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_10__decodeDecimalLitAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_4__extractMainModule(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_filterSepElemsM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isAtom___boxed(lean_object*);
lean_object* l_Lean_ParserDescr_optional(uint8_t, lean_object*);
lean_object* l_Array_mapSepElemsM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_toNat___boxed(lean_object*);
lean_object* l_Lean_identKind___closed__2;
lean_object* l___private_Init_LeanInit_8__decodeHexDigit(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_1__eraseMacroScopesAux___main(lean_object*);
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux(lean_object*);
lean_object* l_Lean_ParserDescr_lookahead(uint8_t, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Syntax_findAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_5__extractMacroScopesAux(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Syntax_isOfKind___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_HasBeq;
lean_object* l___private_Init_LeanInit_13__decodeNameLitAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fieldIdxKind___closed__1;
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main(lean_object*);
uint8_t l_Char_isDigit(uint32_t);
lean_object* l_Lean_charLitKind___closed__2;
lean_object* l_Lean_ParserDescr_many(uint8_t, lean_object*);
lean_object* l_Lean_isGreek___boxed(lean_object*);
uint32_t l_Lean_idEndEscape;
lean_object* l___private_Init_LeanInit_7__decodeOctalLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isIdRest___boxed(lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
uint8_t l_Lean_isIdBeginEscape(uint32_t);
lean_object* l_Lean_ParserDescr_ident(uint8_t);
lean_object* l___private_Init_LeanInit_9__decodeHexLitAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_strLit(uint8_t);
lean_object* l_Lean_Name_HasToString___closed__1;
lean_object* l_Lean_mkNameSimple(lean_object*);
lean_object* l_Lean_isIdFirst___boxed(lean_object*);
lean_object* l_Lean_mkHole___boxed(lean_object*);
lean_object* l_Lean_ParserDescr_andthen___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux___main___at_Array_filterSepElems___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Syntax_findAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_charLitKind___closed__1;
lean_object* l___private_Init_LeanInit_6__decodeBinLitAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_termIdToAntiquot___closed__3;
lean_object* l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__4;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_inhabited;
lean_object* l_Lean_ParserDescr_charLit(uint8_t);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Syntax_identToStrLit(lean_object*);
lean_object* l___private_Init_LeanInit_6__decodeBinLitAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_termIdToAntiquot___closed__1;
lean_object* l___private_Init_LeanInit_12__decodeQuotedChar___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hashable___closed__1;
lean_object* l_Array_filterSepElemsM___boxed(lean_object*);
lean_object* l_Array_filterSepElemsM___at_Array_filterSepElems___spec__1(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo___main___boxed(lean_object*);
lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l_Array_filterSepElems___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeStrLitAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameGenerator_Inhabited;
lean_object* l_Lean_mkTermIdFromIdent___closed__1;
lean_object* l_Lean_ParserDescr_try(uint8_t, lean_object*);
lean_object* l_Lean_nameLitKind;
lean_object* l_Lean_Syntax_termIdToAntiquot___closed__2;
lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l_Substring_takeWhileAux___main___at___private_Init_LeanInit_13__decodeNameLitAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppStx___closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_isSubScriptAlnum___boxed(lean_object*);
lean_object* l_Array_mapSepElems(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_4__extractMainModule___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1(lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind___closed__2;
lean_object* l_Lean_Syntax_getKind___closed__1;
lean_object* l_Lean_Name_hashable;
lean_object* l_Lean_mkTermIdFromIdent___closed__2;
lean_object* l_Lean_Syntax_isSimpleTermId_x3f(lean_object*, uint8_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___boxed(lean_object*);
lean_object* l_Lean_Syntax_strLitToAtom(lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object*);
lean_object* l_Lean_mkStxNumLit(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescrCore_inhabited(uint8_t);
lean_object* l_Lean_Name_HasAppend___closed__1;
lean_object* l_Array_mapSepElems___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_MacroM_monadQuotation___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_termIdToAntiquot___closed__4;
lean_object* l_Lean_ParserDescr_many1(uint8_t, lean_object*);
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___at_Array_mapSepElems___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Array_getSepElems___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_findAux___main(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_6__decodeBinLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_numLitKind;
lean_object* l_Lean_ParserDescr_many___boxed(lean_object*, lean_object*);
lean_object* l_Lean_choiceKind___closed__1;
lean_object* l___private_Init_LeanInit_7__decodeOctalLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_choiceKind___closed__2;
lean_object* l_Lean_MacroM_monadQuotation___lambda__2___boxed(lean_object*);
lean_object* l_Lean_strLitKind;
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Array_getSepElems(lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isSimpleTermId_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_13__decodeNameLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_numLit___boxed(lean_object*);
lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object*);
lean_object* l_Substring_takeWhileAux___main___at___private_Init_LeanInit_13__decodeNameLitAux___main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_many1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Macro_addMacroScope(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux___main___at_Array_filterSepElems___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkTermIdFrom___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*);
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux(lean_object*);
lean_object* l_Lean_firstFrontendMacroScope___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_numLitKind___closed__1;
lean_object* l_Lean_NameGenerator_next(lean_object*);
lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_1__eraseMacroScopesAux(lean_object*);
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_strLitKind___closed__1;
lean_object* l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__5;
lean_object* l_Lean_Syntax_isNatLitAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_NameGenerator_Inhabited___closed__2;
lean_object* l_Lean_Syntax_getArgs___boxed(lean_object*);
lean_object* l_Array_getSepElems___rarg(lean_object*);
lean_object* l___private_Init_LeanInit_1__eraseMacroScopesAux___boxed(lean_object*);
lean_object* l_Lean_reservedMacroScope;
lean_object* l___private_Init_LeanInit_10__decodeDecimalLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNullNode(lean_object*);
lean_object* l_Lean_strLitKind___closed__2;
lean_object* l_Lean_NameGenerator_Inhabited___closed__1;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_ParserDescr_parser(uint8_t, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Array_mapSepElemsM___at_Array_mapSepElems___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_HasToString;
lean_object* l___private_Init_LeanInit_13__decodeNameLitAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_lookahead___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_sepBy(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_choiceKind;
lean_object* l_Lean_charLitKind;
lean_object* l_Substring_takeWhileAux___main___at___private_Init_LeanInit_13__decodeNameLitAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_andthen(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_charLit___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_6__decodeBinLitAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_symbol___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_9__decodeHexLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_numLitKind___closed__2;
lean_object* l_Lean_ParserDescr_node(uint8_t, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l_Lean_ParserDescr_try___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_ident___boxed(lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
lean_object* l_Nat_pred(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___boxed(lean_object*, lean_object*);
lean_object* l_Array_filterSepElemsM(lean_object*);
lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_ParserDescr_node___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_nameLit___boxed(lean_object*);
extern uint8_t l_String_posOfAux___main___closed__2;
lean_object* l_Lean_NameGenerator_mkChild(lean_object*);
lean_object* l_Lean_ParserDescr_parser___boxed(lean_object*, lean_object*, lean_object*);
extern uint8_t l_String_posOfAux___main___closed__1;
lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_2__assembleParts(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_nullKind___closed__1;
lean_object* l_Lean_Syntax_decodeStrLit___boxed(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_nonReservedSymbol___boxed(lean_object*, lean_object*);
uint8_t l_Lean_isIdEndEscape(uint32_t);
lean_object* l_Lean_Syntax_decodeCharLit(lean_object*);
lean_object* l_Lean_MacroScopesView_inhabited___closed__1;
uint8_t l_Char_isAlpha(uint32_t);
uint8_t l_Lean_Syntax_isAtom(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_7__decodeOctalLitAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_MacroM_monadQuotation___closed__3;
uint8_t l_Lean_isLetterLike(uint32_t);
lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main___closed__1;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo___main(lean_object*);
lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l_Lean_isLetterLike___boxed(lean_object*);
lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object*);
lean_object* l_Lean_ParserDescrCore_inhabited___boxed(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes___main(lean_object*);
lean_object* l_Lean_ParserDescr_strLit___boxed(lean_object*);
lean_object* l_Lean_identKind;
lean_object* l_Lean_ParserDescr_sepBy1(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkCTermId(lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_Syntax_inhabited;
lean_object* l_Lean_mkAppStx___closed__5;
lean_object* l_Lean_mkHole(lean_object*);
lean_object* l_Lean_MacroM_monadQuotation___lambda__1___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_3__extractImported(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_5__extractMacroScopesAux___main(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_hasArgs(lean_object*);
lean_object* l_String_quote(lean_object*);
uint8_t l_Char_isAlphanum(uint32_t);
lean_object* l___private_Init_LeanInit_12__decodeQuotedChar(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isTermId_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l_Lean_isGreek(uint32_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* l_Lean_Syntax_getArg___boxed(lean_object*, lean_object*);
lean_object* l_Array_filterSepElems(lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM___at_Array_mapSepElems___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_identToAtom(lean_object*);
lean_object* l_Lean_Name_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_11__decodeNatLitVal___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_11__decodeNatLitVal___closed__1;
lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l___private_Init_LeanInit_7__decodeOctalLitAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameGenerator_curr(lean_object*);
lean_object* l_Lean_Syntax_isTermId_x3f___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__2;
lean_object* l_Lean_mkHole___closed__1;
lean_object* l_Lean_Name_hasMacroScopes___boxed(lean_object*);
lean_object* l_Lean_isIdBeginEscape___boxed(lean_object*);
lean_object* l_Lean_ParserDescr_numLit(uint8_t);
lean_object* l_Lean_mkStxStrLit(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_13__decodeNameLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCAppStx(lean_object*, lean_object*);
lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Name_HasBeq___closed__1;
lean_object* l_Lean_Name_append___main___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_mkTermIdFrom(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeNameLit(lean_object*);
lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object*);
lean_object* l_Lean_ParserDescr_orelse___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isIdEndEscape___boxed(lean_object*);
lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_10__decodeDecimalLitAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_termIdToAntiquot(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeStrLit(lean_object*);
uint8_t l_Lean_isIdFirst(uint32_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
size_t lean_usize_mix_hash(size_t, size_t);
lean_object* l_Lean_Syntax_isNone___boxed(lean_object*);
lean_object* l_Lean_mkCIdentFrom___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkHole___closed__2;
lean_object* l_Lean_mkCIdentFrom___closed__1;
lean_object* l_Lean_Syntax_decodeNameLit___boxed(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_MacroM_monadQuotation___closed__1;
lean_object* l_Lean_nameLitKind___closed__2;
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
lean_object* l_List_foldl___main___at_Lean_MacroScopesView_review___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_sepBy___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported(lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_mkStxLit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___at_Array_mapSepElems___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_toNat(lean_object*);
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux___main(lean_object*);
lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Syntax_getOptional_x3f___boxed(lean_object*);
lean_object* l_Lean_mkCIdentFrom___closed__2;
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes___boxed(lean_object*);
lean_object* l_Lean_mkCTermIdFrom(lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___main___at___private_Init_LeanInit_13__decodeNameLitAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_strLitToAtom___boxed(lean_object*);
lean_object* l_Lean_Syntax_find_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeStrLitAux___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_mkAtomFrom___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_filterSepElemsM___at_Array_filterSepElems___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_ParserDescr_symbol(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_9__decodeHexLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MacroM_monadQuotation___lambda__1(lean_object*);
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux___boxed(lean_object*);
uint8_t l_UInt32_decLe(uint32_t, uint32_t);
lean_object* l_Lean_ParserDescr_optional___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkAppStx___closed__2;
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux___main___boxed(lean_object*);
lean_object* l_Lean_ParserDescr_nonReservedSymbol(lean_object*, uint8_t);
lean_object* l_Lean_Name_hasMacroScopes___main___boxed(lean_object*);
lean_object* l_Lean_Name_hasMacroScopes___main___closed__1;
lean_object* l_Lean_Syntax_findAux(lean_object*, lean_object*);
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
lean_object* l___private_Init_LeanInit_3__extractImported___main(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_string_hash(lean_object*);
lean_object* l_Lean_ParserDescr_sepBy1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_1__eraseMacroScopesAux___main___boxed(lean_object*);
lean_object* l_Lean_Name_append___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isIdRest(uint32_t);
lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
lean_object* l_Lean_Syntax_isIdent___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MacroM_monadQuotation___closed__4;
lean_object* l_Lean_nameLitKind___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__3;
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_ParserDescr_nameLit(uint8_t);
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
uint32_t x_2; uint8_t x_3; uint8_t x_19; uint8_t x_27; uint8_t x_35; uint8_t x_59; 
x_2 = 945;
x_59 = x_2 <= x_1;
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = 0;
x_35 = x_60;
goto block_58;
}
else
{
uint32_t x_61; uint8_t x_62; 
x_61 = 969;
x_62 = x_1 <= x_61;
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = 0;
x_35 = x_63;
goto block_58;
}
else
{
uint32_t x_64; uint8_t x_65; 
x_64 = 955;
x_65 = x_1 == x_64;
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = 1;
return x_66;
}
else
{
uint8_t x_67; 
x_67 = 0;
x_35 = x_67;
goto block_58;
}
}
}
block_18:
{
uint32_t x_4; uint8_t x_5; 
x_4 = 8448;
x_5 = x_4 <= x_1;
if (x_5 == 0)
{
if (x_3 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 119964;
x_7 = x_6 <= x_1;
if (x_7 == 0)
{
return x_3;
}
else
{
uint32_t x_8; uint8_t x_9; 
x_8 = 120223;
x_9 = x_1 <= x_8;
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 1;
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
return x_12;
}
else
{
uint32_t x_15; uint8_t x_16; 
x_15 = 120223;
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
block_26:
{
uint32_t x_20; uint8_t x_21; 
x_20 = 7936;
x_21 = x_20 <= x_1;
if (x_21 == 0)
{
if (x_19 == 0)
{
x_3 = x_19;
goto block_18;
}
else
{
uint8_t x_22; 
x_22 = 1;
return x_22;
}
}
else
{
uint32_t x_23; uint8_t x_24; 
x_23 = 8190;
x_24 = x_1 <= x_23;
if (x_24 == 0)
{
x_3 = x_24;
goto block_18;
}
else
{
uint8_t x_25; 
x_25 = 1;
return x_25;
}
}
}
block_34:
{
uint32_t x_28; uint8_t x_29; 
x_28 = 970;
x_29 = x_28 <= x_1;
if (x_29 == 0)
{
if (x_27 == 0)
{
x_19 = x_27;
goto block_26;
}
else
{
uint8_t x_30; 
x_30 = 1;
return x_30;
}
}
else
{
uint32_t x_31; uint8_t x_32; 
x_31 = 1019;
x_32 = x_1 <= x_31;
if (x_32 == 0)
{
x_19 = x_32;
goto block_26;
}
else
{
uint8_t x_33; 
x_33 = 1;
return x_33;
}
}
}
block_58:
{
uint32_t x_36; uint8_t x_37; 
x_36 = 913;
x_37 = x_36 <= x_1;
if (x_37 == 0)
{
if (x_35 == 0)
{
x_27 = x_35;
goto block_34;
}
else
{
uint32_t x_38; uint8_t x_39; 
x_38 = 928;
x_39 = x_1 == x_38;
if (x_39 == 0)
{
uint32_t x_40; uint8_t x_41; 
x_40 = 931;
x_41 = x_1 == x_40;
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = 1;
return x_42;
}
else
{
uint8_t x_43; 
x_43 = 0;
x_27 = x_43;
goto block_34;
}
}
else
{
uint8_t x_44; 
x_44 = 1;
return x_44;
}
}
}
else
{
uint32_t x_45; uint8_t x_46; 
x_45 = 937;
x_46 = x_1 <= x_45;
if (x_46 == 0)
{
if (x_35 == 0)
{
x_27 = x_35;
goto block_34;
}
else
{
uint32_t x_47; uint8_t x_48; 
x_47 = 931;
x_48 = x_1 == x_47;
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = 1;
return x_49;
}
else
{
uint8_t x_50; 
x_50 = 0;
x_27 = x_50;
goto block_34;
}
}
}
else
{
uint32_t x_51; uint8_t x_52; 
x_51 = 928;
x_52 = x_1 == x_51;
if (x_52 == 0)
{
uint32_t x_53; uint8_t x_54; 
x_53 = 931;
x_54 = x_1 == x_53;
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = 1;
return x_55;
}
else
{
uint8_t x_56; 
x_56 = 0;
x_27 = x_56;
goto block_34;
}
}
else
{
if (x_35 == 0)
{
x_27 = x_35;
goto block_34;
}
else
{
uint8_t x_57; 
x_57 = 1;
return x_57;
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
uint8_t l_Lean_isSubScriptAlnum(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; uint8_t x_19; 
x_2 = 8320;
x_19 = x_2 <= x_1;
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 0;
x_3 = x_20;
goto block_18;
}
else
{
uint32_t x_21; uint8_t x_22; 
x_21 = 8329;
x_22 = x_1 <= x_21;
if (x_22 == 0)
{
x_3 = x_22;
goto block_18;
}
else
{
uint8_t x_23; 
x_23 = 1;
return x_23;
}
}
block_18:
{
uint32_t x_4; uint8_t x_5; 
x_4 = 8336;
x_5 = x_4 <= x_1;
if (x_5 == 0)
{
if (x_3 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 7522;
x_7 = x_6 <= x_1;
if (x_7 == 0)
{
return x_3;
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
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint32_t x_11; uint8_t x_12; 
x_11 = 8348;
x_12 = x_1 <= x_11;
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 7522;
x_14 = x_13 <= x_1;
if (x_14 == 0)
{
return x_12;
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
uint32_t _init_l_Lean_idBeginEscape() {
_start:
{
uint32_t x_1; 
x_1 = 171;
return x_1;
}
}
uint32_t _init_l_Lean_idEndEscape() {
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
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
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
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
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
lean_object* l_Lean_ParserDescr_numLit(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(12, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ParserDescr_numLit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParserDescr_numLit(x_2);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_strLit(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(13, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ParserDescr_strLit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParserDescr_strLit(x_2);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_charLit(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(14, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ParserDescr_charLit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParserDescr_charLit(x_2);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_nameLit(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(15, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ParserDescr_nameLit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParserDescr_nameLit(x_2);
return x_3;
}
}
lean_object* l_Lean_ParserDescr_ident(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(16, 0, 1);
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
x_1 = lean_box(17);
return x_1;
}
}
lean_object* l_Lean_ParserDescr_parser(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(18, 2, 1);
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
lean_object* _init_l_Lean_identKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ident");
return x_1;
}
}
lean_object* _init_l_Lean_identKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_identKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_identKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_identKind___closed__2;
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
lean_object* _init_l_Lean_nameLitKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nameLit");
return x_1;
}
}
lean_object* _init_l_Lean_nameLitKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_nameLitKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_nameLitKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_nameLitKind___closed__2;
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
x_7 = l_Lean_identKind;
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
lean_object* l_Array_findSomeMAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_5 = l_Array_findSomeMAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1(x_3, x_4);
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
lean_object* l_Array_findSomeMAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findSomeMAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1(x_1, x_2);
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
lean_object* _init_l_Lean_reservedMacroScope() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
lean_object* _init_l_Lean_firstFrontendMacroScope___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_reservedMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_firstFrontendMacroScope() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_firstFrontendMacroScope___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Name_hasMacroScopes___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_hyg");
return x_1;
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
x_4 = l_Lean_Name_hasMacroScopes___main___closed__1;
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
lean_object* _init_l___private_Init_LeanInit_1__eraseMacroScopesAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_@");
return x_1;
}
}
lean_object* l___private_Init_LeanInit_1__eraseMacroScopesAux___main(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l___private_Init_LeanInit_1__eraseMacroScopesAux___main___closed__1;
x_7 = lean_string_dec_eq(x_5, x_6);
x_8 = l_coeDecidableEq(x_7);
if (x_8 == 0)
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
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 0);
x_1 = x_10;
goto _start;
}
}
}
}
lean_object* l___private_Init_LeanInit_1__eraseMacroScopesAux___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_LeanInit_1__eraseMacroScopesAux___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_1__eraseMacroScopesAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_LeanInit_1__eraseMacroScopesAux___main(x_1);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_1__eraseMacroScopesAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_LeanInit_1__eraseMacroScopesAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Name_eraseMacroScopes(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = l_Lean_Name_hasMacroScopes___main(x_1);
x_3 = l_coeDecidableEq(x_2);
if (x_3 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_1__eraseMacroScopesAux___main(x_1);
return x_4;
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
lean_object* _init_l_Lean_MacroScopesView_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_MacroScopesView_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MacroScopesView_inhabited___closed__1;
return x_1;
}
}
lean_object* l_List_foldl___main___at_Lean_MacroScopesView_review___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_MacroScopesView_review(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_3 = l_List_isEmpty___rarg(x_2);
x_4 = l_coeDecidableEq(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = l___private_Init_LeanInit_1__eraseMacroScopesAux___main___closed__1;
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l_Lean_Name_append___main(x_7, x_8);
lean_dec(x_7);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_Name_append___main(x_9, x_10);
lean_dec(x_9);
x_12 = l_Lean_Name_hasMacroScopes___main___closed__1;
x_13 = lean_name_mk_string(x_11, x_12);
x_14 = l_List_foldl___main___at_Lean_MacroScopesView_review___spec__1(x_13, x_2);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
return x_15;
}
}
}
lean_object* l___private_Init_LeanInit_2__assembleParts___main(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Init_LeanInit_2__assembleParts(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_LeanInit_2__assembleParts___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_LeanInit_3__extractImported___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_5 = l_Lean_MacroScopesView_inhabited;
x_6 = l_unreachable_x21___rarg(x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = l___private_Init_LeanInit_1__eraseMacroScopesAux___main___closed__1;
x_10 = lean_string_dec_eq(x_8, x_9);
lean_dec(x_8);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_4);
x_3 = x_7;
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = l___private_Init_LeanInit_2__assembleParts___main(x_4, x_14);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_2);
lean_ctor_set(x_16, 3, x_1);
return x_16;
}
}
default: 
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_4);
x_3 = x_17;
x_4 = x_18;
goto _start;
}
}
}
}
lean_object* l___private_Init_LeanInit_3__extractImported(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_LeanInit_3__extractImported___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_LeanInit_4__extractMainModule___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_4 = l_Lean_MacroScopesView_inhabited;
x_5 = l_unreachable_x21___rarg(x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = l___private_Init_LeanInit_1__eraseMacroScopesAux___main___closed__1;
x_9 = lean_string_dec_eq(x_7, x_8);
lean_dec(x_7);
x_10 = l_coeDecidableEq(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_3);
x_2 = x_6;
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = l___private_Init_LeanInit_2__assembleParts___main(x_3, x_13);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_1);
return x_15;
}
}
default: 
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_box(0);
x_17 = l___private_Init_LeanInit_2__assembleParts___main(x_3, x_16);
x_18 = lean_box(0);
x_19 = l___private_Init_LeanInit_3__extractImported___main(x_1, x_17, x_2, x_18);
return x_19;
}
}
}
}
lean_object* l___private_Init_LeanInit_4__extractMainModule(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_4__extractMainModule___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_5__extractMacroScopesAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
lean_dec(x_2);
x_3 = l_Lean_MacroScopesView_inhabited;
x_4 = l_unreachable_x21___rarg(x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = l___private_Init_LeanInit_4__extractMainModule___main(x_2, x_5, x_6);
return x_7;
}
default: 
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
x_1 = x_8;
x_2 = x_10;
goto _start;
}
}
}
}
lean_object* l___private_Init_LeanInit_5__extractMacroScopesAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_LeanInit_5__extractMacroScopesAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_extractMacroScopes(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = l_Lean_Name_hasMacroScopes___main(x_1);
x_3 = l_coeDecidableEq(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set(x_6, 3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l___private_Init_LeanInit_5__extractMacroScopesAux___main(x_1, x_7);
return x_8;
}
}
}
lean_object* l_Lean_addMacroScope(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; 
x_4 = l_Lean_Name_hasMacroScopes___main(x_2);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l___private_Init_LeanInit_1__eraseMacroScopesAux___main___closed__1;
x_7 = lean_name_mk_string(x_2, x_6);
x_8 = l_Lean_Name_append___main(x_7, x_1);
lean_dec(x_7);
x_9 = l_Lean_Name_hasMacroScopes___main___closed__1;
x_10 = lean_name_mk_string(x_8, x_9);
x_11 = lean_name_mk_numeral(x_10, x_3);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_inc(x_2);
x_12 = l_Lean_extractMacroScopes(x_2);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_name_eq(x_16, x_1);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_20 = l_Lean_Name_append___main(x_15, x_16);
lean_dec(x_15);
x_21 = l_List_foldl___main___at_Lean_MacroScopesView_review___spec__1(x_20, x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_12, 3, x_23);
lean_ctor_set(x_12, 2, x_1);
lean_ctor_set(x_12, 1, x_21);
x_24 = l_Lean_MacroScopesView_review(x_12);
return x_24;
}
else
{
lean_object* x_25; 
lean_free_object(x_12);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_25 = lean_name_mk_numeral(x_2, x_3);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
x_28 = lean_ctor_get(x_12, 2);
x_29 = lean_ctor_get(x_12, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_30 = lean_name_eq(x_28, x_1);
x_31 = l_coeDecidableEq(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_32 = l_Lean_Name_append___main(x_27, x_28);
lean_dec(x_27);
x_33 = l_List_foldl___main___at_Lean_MacroScopesView_review___spec__1(x_32, x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_3);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_1);
lean_ctor_set(x_36, 3, x_35);
x_37 = l_Lean_MacroScopesView_review(x_36);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_38 = lean_name_mk_numeral(x_2, x_3);
return x_38;
}
}
}
}
}
lean_object* l_Lean_Macro_addMacroScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_addMacroScope(x_3, x_1, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
lean_object* _init_l_Lean_Macro_throwUnsupported___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Macro_throwUnsupported(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Macro_throwUnsupported___closed__1;
return x_3;
}
}
lean_object* l_Lean_Macro_throwUnsupported___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Macro_throwUnsupported(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_MacroM_monadQuotation___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* l_Lean_MacroM_monadQuotation___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* l_Lean_MacroM_monadQuotation___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_MacroM_monadQuotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MacroM_monadQuotation___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_MacroM_monadQuotation___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MacroM_monadQuotation___lambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_MacroM_monadQuotation___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MacroM_monadQuotation___lambda__3), 3, 0);
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
lean_object* l_Lean_MacroM_monadQuotation___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MacroM_monadQuotation___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_MacroM_monadQuotation___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_MacroM_monadQuotation___lambda__2(x_1);
lean_dec(x_1);
return x_2;
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
x_1 = lean_mk_string("_internal");
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = l_Lean_Syntax_getHeadInfo___main(x_1);
x_4 = l_Lean_mkCIdentFrom___closed__2;
x_5 = l_Lean_reservedMacroScope;
lean_inc(x_2);
x_6 = l_Lean_addMacroScope(x_4, x_2, x_5);
x_7 = l_Lean_Name_toString___closed__1;
lean_inc(x_6);
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_6);
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
x_15 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_6);
lean_ctor_set(x_15, 3, x_14);
return x_15;
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
uint8_t x_4; uint8_t x_5; 
x_4 = lean_string_utf8_at_end(x_1, x_2);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; uint8_t x_33; 
x_6 = lean_string_utf8_get(x_1, x_2);
x_7 = 48;
x_33 = x_6 == x_7;
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = 0;
x_8 = x_34;
goto block_32;
}
else
{
uint8_t x_35; 
x_35 = 1;
x_8 = x_35;
goto block_32;
}
block_32:
{
uint8_t x_9; 
x_9 = l_coeDecidableEq(x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 49;
x_11 = x_6 == x_10;
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_String_posOfAux___main___closed__1;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_mul(x_15, x_3);
lean_dec(x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_16, x_17);
lean_dec(x_16);
x_2 = x_14;
x_3 = x_18;
goto _start;
}
}
else
{
uint8_t x_20; 
x_20 = l_String_posOfAux___main___closed__2;
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_box(0);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_nat_mul(x_23, x_3);
lean_dec(x_3);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_24, x_25);
lean_dec(x_24);
x_2 = x_22;
x_3 = x_26;
goto _start;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_29 = lean_unsigned_to_nat(2u);
x_30 = lean_nat_mul(x_29, x_3);
lean_dec(x_3);
x_2 = x_28;
x_3 = x_30;
goto _start;
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_2);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_3);
return x_36;
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
uint8_t x_4; uint8_t x_5; 
x_4 = lean_string_utf8_at_end(x_1, x_2);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_2);
x_7 = 48;
x_8 = x_7 <= x_6;
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_String_posOfAux___main___closed__1;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_12 = lean_unsigned_to_nat(8u);
x_13 = lean_nat_mul(x_12, x_3);
lean_dec(x_3);
x_14 = lean_uint32_to_nat(x_6);
x_15 = lean_nat_add(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(48u);
x_17 = lean_nat_sub(x_15, x_16);
lean_dec(x_15);
x_2 = x_11;
x_3 = x_17;
goto _start;
}
}
else
{
uint32_t x_19; uint8_t x_20; uint8_t x_21; 
x_19 = 55;
x_20 = x_6 <= x_19;
x_21 = l_coeDecidableEq(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_24 = lean_unsigned_to_nat(8u);
x_25 = lean_nat_mul(x_24, x_3);
lean_dec(x_3);
x_26 = lean_uint32_to_nat(x_6);
x_27 = lean_nat_add(x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
x_28 = lean_unsigned_to_nat(48u);
x_29 = lean_nat_sub(x_27, x_28);
lean_dec(x_27);
x_2 = x_23;
x_3 = x_29;
goto _start;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_2);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_3);
return x_31;
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
uint32_t x_3; lean_object* x_4; uint32_t x_5; uint8_t x_6; uint8_t x_51; 
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = lean_string_utf8_next(x_1, x_2);
x_5 = 48;
x_51 = x_5 <= x_3;
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = 0;
x_6 = x_52;
goto block_50;
}
else
{
uint32_t x_53; uint8_t x_54; 
x_53 = 57;
x_54 = x_3 <= x_53;
x_6 = x_54;
goto block_50;
}
block_50:
{
uint8_t x_7; 
x_7 = l_coeDecidableEq(x_6);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; uint8_t x_41; 
x_8 = 97;
x_41 = x_8 <= x_3;
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = 0;
x_9 = x_42;
goto block_40;
}
else
{
uint32_t x_43; uint8_t x_44; 
x_43 = 102;
x_44 = x_3 <= x_43;
x_9 = x_44;
goto block_40;
}
block_40:
{
uint8_t x_10; 
x_10 = l_coeDecidableEq(x_9);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 65;
x_12 = x_11 <= x_3;
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_String_posOfAux___main___closed__1;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_uint32_to_nat(x_3);
x_16 = lean_unsigned_to_nat(10u);
x_17 = lean_nat_add(x_16, x_15);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(65u);
x_19 = lean_nat_sub(x_17, x_18);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
uint32_t x_22; uint8_t x_23; uint8_t x_24; 
x_22 = 70;
x_23 = x_3 <= x_22;
x_24 = l_coeDecidableEq(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_4);
x_25 = lean_box(0);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_uint32_to_nat(x_3);
x_27 = lean_unsigned_to_nat(10u);
x_28 = lean_nat_add(x_27, x_26);
lean_dec(x_26);
x_29 = lean_unsigned_to_nat(65u);
x_30 = lean_nat_sub(x_28, x_29);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_uint32_to_nat(x_3);
x_34 = lean_unsigned_to_nat(10u);
x_35 = lean_nat_add(x_34, x_33);
lean_dec(x_33);
x_36 = lean_unsigned_to_nat(97u);
x_37 = lean_nat_sub(x_35, x_36);
lean_dec(x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_4);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_uint32_to_nat(x_3);
x_46 = lean_unsigned_to_nat(48u);
x_47 = lean_nat_sub(x_45, x_46);
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_4);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
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
uint8_t x_4; uint8_t x_5; 
x_4 = lean_string_utf8_at_end(x_1, x_2);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l___private_Init_LeanInit_8__decodeHexDigit(x_1, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(16u);
x_12 = lean_nat_mul(x_11, x_3);
lean_dec(x_3);
x_13 = lean_nat_add(x_12, x_9);
lean_dec(x_9);
lean_dec(x_12);
x_2 = x_10;
x_3 = x_13;
goto _start;
}
}
else
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_3);
return x_15;
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
uint8_t x_4; uint8_t x_5; 
x_4 = lean_string_utf8_at_end(x_1, x_2);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_2);
x_7 = 48;
x_8 = x_7 <= x_6;
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_String_posOfAux___main___closed__1;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_12 = lean_unsigned_to_nat(10u);
x_13 = lean_nat_mul(x_12, x_3);
lean_dec(x_3);
x_14 = lean_uint32_to_nat(x_6);
x_15 = lean_nat_add(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(48u);
x_17 = lean_nat_sub(x_15, x_16);
lean_dec(x_15);
x_2 = x_11;
x_3 = x_17;
goto _start;
}
}
else
{
uint32_t x_19; uint8_t x_20; uint8_t x_21; 
x_19 = 57;
x_20 = x_6 <= x_19;
x_21 = l_coeDecidableEq(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_24 = lean_unsigned_to_nat(10u);
x_25 = lean_nat_mul(x_24, x_3);
lean_dec(x_3);
x_26 = lean_uint32_to_nat(x_6);
x_27 = lean_nat_add(x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
x_28 = lean_unsigned_to_nat(48u);
x_29 = lean_nat_sub(x_27, x_28);
lean_dec(x_27);
x_2 = x_23;
x_3 = x_29;
goto _start;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_2);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_3);
return x_31;
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
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_2 = lean_string_length(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; uint8_t x_92; 
x_6 = lean_string_utf8_get(x_1, x_3);
x_7 = 48;
x_92 = x_6 == x_7;
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = 0;
x_8 = x_93;
goto block_91;
}
else
{
uint8_t x_94; 
x_94 = 1;
x_8 = x_94;
goto block_91;
}
block_91:
{
uint8_t x_9; 
x_9 = l_coeDecidableEq(x_8);
if (x_9 == 0)
{
uint8_t x_10; uint8_t x_11; 
lean_dec(x_2);
x_10 = l_Char_isDigit(x_6);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l___private_Init_LeanInit_10__decodeDecimalLitAux___main(x_1, x_3, x_3);
return x_13;
}
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_dec_eq(x_2, x_14);
lean_dec(x_2);
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; uint32_t x_52; uint8_t x_53; uint8_t x_87; 
x_17 = lean_string_utf8_get(x_1, x_14);
x_52 = 120;
x_87 = x_17 == x_52;
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = 0;
x_53 = x_88;
goto block_86;
}
else
{
uint8_t x_89; 
x_89 = 1;
x_53 = x_89;
goto block_86;
}
block_51:
{
uint8_t x_19; 
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
uint32_t x_20; uint8_t x_21; uint8_t x_46; 
x_20 = 111;
x_46 = x_17 == x_20;
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = 0;
x_21 = x_47;
goto block_45;
}
else
{
uint8_t x_48; 
x_48 = 1;
x_21 = x_48;
goto block_45;
}
block_45:
{
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 79;
x_23 = x_17 == x_22;
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_String_posOfAux___main___closed__1;
if (x_24 == 0)
{
uint8_t x_25; uint8_t x_26; 
x_25 = l_Char_isDigit(x_17);
x_26 = l_coeDecidableEq(x_25);
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
uint8_t x_31; 
x_31 = l_String_posOfAux___main___closed__2;
if (x_31 == 0)
{
uint8_t x_32; uint8_t x_33; 
x_32 = l_Char_isDigit(x_17);
x_33 = l_coeDecidableEq(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_box(0);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = l___private_Init_LeanInit_10__decodeDecimalLitAux___main(x_1, x_3, x_3);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_unsigned_to_nat(2u);
x_37 = l___private_Init_LeanInit_7__decodeOctalLitAux___main(x_1, x_36, x_3);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = l_String_posOfAux___main___closed__2;
if (x_38 == 0)
{
uint8_t x_39; uint8_t x_40; 
x_39 = l_Char_isDigit(x_17);
x_40 = l_coeDecidableEq(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_box(0);
return x_41;
}
else
{
lean_object* x_42; 
x_42 = l___private_Init_LeanInit_10__decodeDecimalLitAux___main(x_1, x_3, x_3);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_unsigned_to_nat(2u);
x_44 = l___private_Init_LeanInit_7__decodeOctalLitAux___main(x_1, x_43, x_3);
return x_44;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_unsigned_to_nat(2u);
x_50 = l___private_Init_LeanInit_6__decodeBinLitAux___main(x_1, x_49, x_3);
return x_50;
}
}
block_86:
{
if (x_53 == 0)
{
uint32_t x_54; uint8_t x_55; 
x_54 = 88;
x_55 = x_17 == x_54;
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = l_String_posOfAux___main___closed__1;
if (x_56 == 0)
{
uint32_t x_57; uint8_t x_58; 
x_57 = 98;
x_58 = x_17 == x_57;
if (x_58 == 0)
{
uint32_t x_59; uint8_t x_60; 
x_59 = 66;
x_60 = x_17 == x_59;
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = 0;
x_18 = x_61;
goto block_51;
}
else
{
uint8_t x_62; 
x_62 = 1;
x_18 = x_62;
goto block_51;
}
}
else
{
uint8_t x_63; 
x_63 = 1;
x_18 = x_63;
goto block_51;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_unsigned_to_nat(2u);
x_65 = l___private_Init_LeanInit_9__decodeHexLitAux___main(x_1, x_64, x_3);
return x_65;
}
}
else
{
uint8_t x_66; 
x_66 = l_String_posOfAux___main___closed__2;
if (x_66 == 0)
{
uint32_t x_67; uint8_t x_68; 
x_67 = 98;
x_68 = x_17 == x_67;
if (x_68 == 0)
{
uint32_t x_69; uint8_t x_70; 
x_69 = 66;
x_70 = x_17 == x_69;
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = 0;
x_18 = x_71;
goto block_51;
}
else
{
uint8_t x_72; 
x_72 = 1;
x_18 = x_72;
goto block_51;
}
}
else
{
uint8_t x_73; 
x_73 = 1;
x_18 = x_73;
goto block_51;
}
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_unsigned_to_nat(2u);
x_75 = l___private_Init_LeanInit_9__decodeHexLitAux___main(x_1, x_74, x_3);
return x_75;
}
}
}
else
{
uint8_t x_76; 
x_76 = l_String_posOfAux___main___closed__2;
if (x_76 == 0)
{
uint32_t x_77; uint8_t x_78; 
x_77 = 98;
x_78 = x_17 == x_77;
if (x_78 == 0)
{
uint32_t x_79; uint8_t x_80; 
x_79 = 66;
x_80 = x_17 == x_79;
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = 0;
x_18 = x_81;
goto block_51;
}
else
{
uint8_t x_82; 
x_82 = 1;
x_18 = x_82;
goto block_51;
}
}
else
{
uint8_t x_83; 
x_83 = 1;
x_18 = x_83;
goto block_51;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_unsigned_to_nat(2u);
x_85 = l___private_Init_LeanInit_9__decodeHexLitAux___main(x_1, x_84, x_3);
return x_85;
}
}
}
}
else
{
lean_object* x_90; 
x_90 = l___private_Init_LeanInit_11__decodeNatLitVal___closed__1;
return x_90;
}
}
}
}
else
{
lean_object* x_95; 
lean_dec(x_2);
x_95 = lean_box(0);
return x_95;
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
uint8_t x_6; 
x_6 = l_String_posOfAux___main___closed__1;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Syntax_inhabited;
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get(x_8, x_4, x_9);
if (lean_obj_tag(x_10) == 2)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_box(0);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_14 = lean_array_get_size(x_4);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
x_17 = l_coeDecidableEq(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Lean_Syntax_inhabited;
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get(x_19, x_4, x_20);
if (lean_obj_tag(x_21) == 2)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_21);
x_24 = lean_box(0);
return x_24;
}
}
}
}
else
{
lean_object* x_25; 
x_25 = lean_box(0);
return x_25;
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
lean_object* l_Lean_Syntax_isNatLitAux(lean_object* x_1, lean_object* x_2) {
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
x_6 = l___private_Init_LeanInit_11__decodeNatLitVal(x_5);
lean_dec(x_5);
return x_6;
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
uint32_t x_3; lean_object* x_4; lean_object* x_5; uint32_t x_119; uint8_t x_120; 
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = lean_string_utf8_next(x_1, x_2);
x_119 = 92;
x_120 = x_3 == x_119;
if (x_120 == 0)
{
uint8_t x_121; 
x_121 = l_String_posOfAux___main___closed__1;
if (x_121 == 0)
{
uint32_t x_122; uint8_t x_123; 
x_122 = 34;
x_123 = x_3 == x_122;
if (x_123 == 0)
{
lean_object* x_124; 
x_124 = lean_box(0);
x_5 = x_124;
goto block_118;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__4;
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_4);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__5;
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_4);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
else
{
uint8_t x_131; 
x_131 = l_String_posOfAux___main___closed__2;
if (x_131 == 0)
{
uint32_t x_132; uint8_t x_133; 
x_132 = 34;
x_133 = x_3 == x_132;
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_box(0);
x_5 = x_134;
goto block_118;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__4;
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_4);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__5;
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_4);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
return x_140;
}
}
block_118:
{
uint32_t x_6; uint8_t x_7; 
lean_dec(x_5);
x_6 = 39;
x_7 = x_3 == x_6;
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 110;
x_9 = x_3 == x_8;
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 116;
x_11 = x_3 == x_10;
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 120;
x_13 = x_3 == x_12;
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 117;
x_15 = x_3 == x_14;
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_4);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l___private_Init_LeanInit_8__decodeHexDigit(x_1, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Init_LeanInit_8__decodeHexDigit(x_1, x_21);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_20);
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
x_27 = l___private_Init_LeanInit_8__decodeHexDigit(x_1, x_26);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec(x_25);
lean_dec(x_20);
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
x_32 = l___private_Init_LeanInit_8__decodeHexDigit(x_1, x_31);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_20);
x_33 = lean_box(0);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint32_t x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_unsigned_to_nat(16u);
x_39 = lean_nat_mul(x_38, x_20);
lean_dec(x_20);
x_40 = lean_nat_add(x_39, x_25);
lean_dec(x_25);
lean_dec(x_39);
x_41 = lean_nat_mul(x_38, x_40);
lean_dec(x_40);
x_42 = lean_nat_add(x_41, x_30);
lean_dec(x_30);
lean_dec(x_41);
x_43 = lean_nat_mul(x_38, x_42);
lean_dec(x_42);
x_44 = lean_nat_add(x_43, x_37);
lean_dec(x_37);
lean_dec(x_43);
x_45 = l_Char_ofNat(x_44);
lean_dec(x_44);
x_46 = lean_box_uint32(x_45);
lean_ctor_set(x_35, 0, x_46);
return x_32;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint32_t x_56; lean_object* x_57; lean_object* x_58; 
x_47 = lean_ctor_get(x_35, 0);
x_48 = lean_ctor_get(x_35, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_35);
x_49 = lean_unsigned_to_nat(16u);
x_50 = lean_nat_mul(x_49, x_20);
lean_dec(x_20);
x_51 = lean_nat_add(x_50, x_25);
lean_dec(x_25);
lean_dec(x_50);
x_52 = lean_nat_mul(x_49, x_51);
lean_dec(x_51);
x_53 = lean_nat_add(x_52, x_30);
lean_dec(x_30);
lean_dec(x_52);
x_54 = lean_nat_mul(x_49, x_53);
lean_dec(x_53);
x_55 = lean_nat_add(x_54, x_47);
lean_dec(x_47);
lean_dec(x_54);
x_56 = l_Char_ofNat(x_55);
lean_dec(x_55);
x_57 = lean_box_uint32(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_48);
lean_ctor_set(x_32, 0, x_58);
return x_32;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint32_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_59 = lean_ctor_get(x_32, 0);
lean_inc(x_59);
lean_dec(x_32);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
x_63 = lean_unsigned_to_nat(16u);
x_64 = lean_nat_mul(x_63, x_20);
lean_dec(x_20);
x_65 = lean_nat_add(x_64, x_25);
lean_dec(x_25);
lean_dec(x_64);
x_66 = lean_nat_mul(x_63, x_65);
lean_dec(x_65);
x_67 = lean_nat_add(x_66, x_30);
lean_dec(x_30);
lean_dec(x_66);
x_68 = lean_nat_mul(x_63, x_67);
lean_dec(x_67);
x_69 = lean_nat_add(x_68, x_60);
lean_dec(x_60);
lean_dec(x_68);
x_70 = l_Char_ofNat(x_69);
lean_dec(x_69);
x_71 = lean_box_uint32(x_70);
if (lean_is_scalar(x_62)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_62;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_61);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
}
}
}
}
else
{
lean_object* x_74; 
x_74 = l___private_Init_LeanInit_8__decodeHexDigit(x_1, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_box(0);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l___private_Init_LeanInit_8__decodeHexDigit(x_1, x_78);
lean_dec(x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
lean_dec(x_77);
x_80 = lean_box(0);
return x_80;
}
else
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_79, 0);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint32_t x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = lean_unsigned_to_nat(16u);
x_86 = lean_nat_mul(x_85, x_77);
lean_dec(x_77);
x_87 = lean_nat_add(x_86, x_84);
lean_dec(x_84);
lean_dec(x_86);
x_88 = l_Char_ofNat(x_87);
lean_dec(x_87);
x_89 = lean_box_uint32(x_88);
lean_ctor_set(x_82, 0, x_89);
return x_79;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint32_t x_95; lean_object* x_96; lean_object* x_97; 
x_90 = lean_ctor_get(x_82, 0);
x_91 = lean_ctor_get(x_82, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_82);
x_92 = lean_unsigned_to_nat(16u);
x_93 = lean_nat_mul(x_92, x_77);
lean_dec(x_77);
x_94 = lean_nat_add(x_93, x_90);
lean_dec(x_90);
lean_dec(x_93);
x_95 = l_Char_ofNat(x_94);
lean_dec(x_94);
x_96 = lean_box_uint32(x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_91);
lean_ctor_set(x_79, 0, x_97);
return x_79;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint32_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_98 = lean_ctor_get(x_79, 0);
lean_inc(x_98);
lean_dec(x_79);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
x_102 = lean_unsigned_to_nat(16u);
x_103 = lean_nat_mul(x_102, x_77);
lean_dec(x_77);
x_104 = lean_nat_add(x_103, x_99);
lean_dec(x_99);
lean_dec(x_103);
x_105 = l_Char_ofNat(x_104);
lean_dec(x_104);
x_106 = lean_box_uint32(x_105);
if (lean_is_scalar(x_101)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_101;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_100);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__1;
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_4);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__2;
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
x_115 = l___private_Init_LeanInit_12__decodeQuotedChar___boxed__const__3;
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_4);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
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
uint32_t x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; uint8_t x_35; 
x_4 = lean_string_utf8_get(x_1, x_2);
x_5 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_6 = 34;
x_35 = x_4 == x_6;
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = 0;
x_7 = x_36;
goto block_34;
}
else
{
uint8_t x_37; 
x_37 = 1;
x_7 = x_37;
goto block_34;
}
block_34:
{
uint8_t x_8; 
x_8 = l_coeDecidableEq(x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 92;
x_10 = x_4 == x_9;
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_String_posOfAux___main___closed__1;
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_string_push(x_3, x_4);
x_2 = x_5;
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = l___private_Init_LeanInit_12__decodeQuotedChar(x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unbox_uint32(x_17);
lean_dec(x_17);
x_20 = lean_string_push(x_3, x_19);
x_2 = x_18;
x_3 = x_20;
goto _start;
}
}
}
else
{
uint8_t x_22; 
x_22 = l_String_posOfAux___main___closed__2;
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_string_push(x_3, x_4);
x_2 = x_5;
x_3 = x_23;
goto _start;
}
else
{
lean_object* x_25; 
x_25 = l___private_Init_LeanInit_12__decodeQuotedChar(x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec(x_3);
x_26 = lean_box(0);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint32_t x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_unbox_uint32(x_28);
lean_dec(x_28);
x_31 = lean_string_push(x_3, x_30);
x_2 = x_29;
x_3 = x_31;
goto _start;
}
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_5);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_3);
return x_33;
}
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
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_strLitKind;
x_3 = l_Lean_Syntax_isLit_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_String_splitAux___main___closed__1;
x_7 = l_Lean_Syntax_decodeStrLitAux___main(x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
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
uint8_t x_6; 
x_6 = l_String_posOfAux___main___closed__1;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box_uint32(x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(2u);
x_10 = l___private_Init_LeanInit_12__decodeQuotedChar(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
else
{
uint8_t x_18; 
x_18 = l_String_posOfAux___main___closed__2;
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box_uint32(x_3);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_unsigned_to_nat(2u);
x_22 = l___private_Init_LeanInit_12__decodeQuotedChar(x_1, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_box(0);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
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
lean_object* l_Substring_takeWhileAux___main___at___private_Init_LeanInit_13__decodeNameLitAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; 
x_4 = lean_nat_dec_eq(x_3, x_2);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_3);
x_7 = l_Lean_isIdRest(x_6);
x_8 = l_coeDecidableEq(x_7);
if (x_8 == 0)
{
return x_3;
}
else
{
lean_object* x_9; 
x_9 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_9;
goto _start;
}
}
else
{
return x_3;
}
}
}
lean_object* l_Substring_takeWhileAux___main___at___private_Init_LeanInit_13__decodeNameLitAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; 
x_4 = lean_nat_dec_eq(x_3, x_2);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = lean_string_utf8_get(x_1, x_3);
x_7 = l_Lean_isIdEndEscape(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_String_posOfAux___main___closed__2;
if (x_8 == 0)
{
return x_3;
}
else
{
lean_object* x_9; 
x_9 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_9;
goto _start;
}
}
else
{
uint8_t x_11; 
x_11 = l_String_posOfAux___main___closed__1;
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; 
x_12 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
}
}
else
{
return x_3;
}
}
}
lean_object* l___private_Init_LeanInit_13__decodeNameLitAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint32_t x_24; uint8_t x_25; uint8_t x_26; 
x_24 = lean_string_utf8_get(x_1, x_2);
x_25 = l_Lean_isIdBeginEscape(x_24);
x_26 = l_coeDecidableEq(x_25);
if (x_26 == 0)
{
uint8_t x_27; uint8_t x_28; 
x_27 = l_Lean_isIdFirst(x_24);
x_28 = l_coeDecidableEq(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_box(0);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_string_utf8_byte_size(x_1);
lean_inc(x_2);
x_31 = l_Substring_takeWhileAux___main___at___private_Init_LeanInit_13__decodeNameLitAux___main___spec__1(x_1, x_30, x_2);
lean_dec(x_30);
x_32 = lean_string_utf8_extract(x_1, x_2, x_31);
lean_dec(x_2);
x_33 = lean_name_mk_string(x_3, x_32);
x_4 = x_31;
x_5 = x_33;
goto block_23;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint32_t x_37; uint8_t x_38; 
x_34 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_35 = lean_string_utf8_byte_size(x_1);
lean_inc(x_34);
x_36 = l_Substring_takeWhileAux___main___at___private_Init_LeanInit_13__decodeNameLitAux___main___spec__2(x_1, x_35, x_34);
lean_dec(x_35);
x_37 = lean_string_utf8_get(x_1, x_36);
x_38 = l_Lean_isIdEndEscape(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_String_posOfAux___main___closed__2;
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_string_utf8_next(x_1, x_36);
x_41 = lean_string_utf8_extract(x_1, x_34, x_36);
lean_dec(x_36);
lean_dec(x_34);
x_42 = lean_name_mk_string(x_3, x_41);
x_4 = x_40;
x_5 = x_42;
goto block_23;
}
else
{
lean_object* x_43; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_3);
x_43 = lean_box(0);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = l_String_posOfAux___main___closed__1;
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_string_utf8_next(x_1, x_36);
x_46 = lean_string_utf8_extract(x_1, x_34, x_36);
lean_dec(x_36);
lean_dec(x_34);
x_47 = lean_name_mk_string(x_3, x_46);
x_4 = x_45;
x_5 = x_47;
goto block_23;
}
else
{
lean_object* x_48; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_3);
x_48 = lean_box(0);
return x_48;
}
}
}
block_23:
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_4);
x_7 = 46;
x_8 = x_6 == x_7;
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_String_posOfAux___main___closed__1;
if (x_9 == 0)
{
uint8_t x_10; uint8_t x_11; 
x_10 = lean_string_utf8_at_end(x_1, x_4);
lean_dec(x_4);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_5);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
}
else
{
lean_object* x_14; 
x_14 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_2 = x_14;
x_3 = x_5;
goto _start;
}
}
else
{
uint8_t x_16; 
x_16 = l_String_posOfAux___main___closed__2;
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; 
x_17 = lean_string_utf8_at_end(x_1, x_4);
lean_dec(x_4);
x_18 = l_coeDecidableEq(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_5);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_2 = x_21;
x_3 = x_5;
goto _start;
}
}
}
}
}
lean_object* l_Substring_takeWhileAux___main___at___private_Init_LeanInit_13__decodeNameLitAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___main___at___private_Init_LeanInit_13__decodeNameLitAux___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Substring_takeWhileAux___main___at___private_Init_LeanInit_13__decodeNameLitAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___main___at___private_Init_LeanInit_13__decodeNameLitAux___main___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_13__decodeNameLitAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_13__decodeNameLitAux___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_13__decodeNameLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_13__decodeNameLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_13__decodeNameLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_13__decodeNameLitAux(x_1, x_2, x_3);
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
uint8_t x_6; 
x_6 = l_String_posOfAux___main___closed__1;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_box(0);
x_10 = l___private_Init_LeanInit_13__decodeNameLitAux___main(x_1, x_8, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = l_String_posOfAux___main___closed__2;
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_box(0);
x_15 = l___private_Init_LeanInit_13__decodeNameLitAux___main(x_1, x_13, x_14);
return x_15;
}
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
uint8_t l_Lean_Syntax_isNone(lean_object* x_1) {
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
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
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
uint8_t x_6; 
x_6 = l_String_posOfAux___main___closed__1;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Syntax_inhabited;
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get(x_8, x_3, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
x_15 = l_coeDecidableEq(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = l_Lean_Syntax_inhabited;
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get(x_17, x_3, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; 
x_21 = lean_box(0);
return x_21;
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
lean_object* l_Lean_Syntax_isTermId_x3f(lean_object* x_1, uint8_t x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_mkTermIdFromIdent___closed__2;
x_6 = lean_name_eq(x_3, x_5);
lean_dec(x_3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_String_posOfAux___main___closed__1;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = l_Lean_Syntax_inhabited;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get(x_9, x_4, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_array_get(x_9, x_4, x_12);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_16 = lean_array_get_size(x_4);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_16);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_4);
x_20 = lean_box(0);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = l_Lean_Syntax_inhabited;
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get(x_21, x_4, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_array_get(x_21, x_4, x_24);
lean_dec(x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
case 3:
{
uint8_t x_28; 
x_28 = l_coeDecidableEq(x_2);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_1);
x_29 = lean_box(0);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lean_mkOptionalNode___closed__1;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
default: 
{
lean_object* x_33; 
lean_dec(x_1);
x_33 = lean_box(0);
return x_33;
}
}
}
}
lean_object* l_Lean_Syntax_isTermId_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Syntax_isTermId_x3f(x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_isSimpleTermId_x3f(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_isTermId_x3f(x_1, x_2);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Syntax_isNone(x_8);
lean_dec(x_8);
x_10 = l_coeDecidableEq(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_free_object(x_3);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_13);
return x_18;
}
}
}
}
}
lean_object* l_Lean_Syntax_isSimpleTermId_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Syntax_isSimpleTermId_x3f(x_1, x_3);
return x_4;
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Syntax_findAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
x_8 = l_Lean_Syntax_findAux___main(x_1, x_7);
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
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
}
lean_object* l_Lean_Syntax_findAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_2);
x_11 = lean_apply_1(x_1, x_2);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
x_13 = l_coeDecidableEq(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_findSomeMAux___main___at_Lean_Syntax_findAux___main___spec__1(x_1, x_10, x_14);
lean_dec(x_10);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = lean_box(0);
x_3 = x_17;
goto block_9;
}
block_9:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; 
lean_dec(x_3);
lean_inc(x_2);
x_4 = lean_apply_1(x_1, x_2);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_coeDecidableEq(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
}
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Syntax_findAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findSomeMAux___main___at_Lean_Syntax_findAux___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Syntax_findAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_findAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_findAux___main(x_2, x_1);
return x_3;
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
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_add(x_1, x_8);
lean_dec(x_1);
x_10 = l___private_Init_LeanInit_14__filterSepElemsMAux___main___rarg(x_2, x_3, x_4, x_9, x_5);
return x_10;
}
else
{
uint8_t x_11; uint8_t x_12; 
x_11 = l_Array_isEmpty___rarg(x_5);
x_12 = l_coeDecidableEq(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_1);
x_15 = lean_nat_sub(x_1, lean_box(1));
x_16 = lean_array_fget(x_3, x_15);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_add(x_1, x_17);
lean_dec(x_1);
x_19 = lean_array_push(x_5, x_16);
x_20 = lean_array_push(x_19, x_6);
x_21 = l___private_Init_LeanInit_14__filterSepElemsMAux___main___rarg(x_2, x_3, x_4, x_18, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_nat_add(x_1, x_22);
lean_dec(x_1);
x_24 = lean_array_push(x_5, x_6);
x_25 = l___private_Init_LeanInit_14__filterSepElemsMAux___main___rarg(x_2, x_3, x_4, x_23, x_24);
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
x_29 = l___private_Init_LeanInit_14__filterSepElemsMAux___main___rarg(x_2, x_3, x_4, x_27, x_28);
return x_29;
}
}
}
}
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_14 = lean_alloc_closure((void*)(l___private_Init_LeanInit_14__filterSepElemsMAux___main___rarg___lambda__1___boxed), 7, 6);
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
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_14__filterSepElemsMAux___main___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l___private_Init_LeanInit_14__filterSepElemsMAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_LeanInit_14__filterSepElemsMAux___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_LeanInit_14__filterSepElemsMAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_14__filterSepElemsMAux___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_LeanInit_14__filterSepElemsMAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_filterSepElemsM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_empty___closed__1;
x_6 = l___private_Init_LeanInit_14__filterSepElemsMAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
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
lean_object* l_Array_filterSepElemsM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_filterSepElemsM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux___main___at_Array_filterSepElems___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
uint8_t x_13; uint8_t x_14; 
x_13 = l_Array_isEmpty___rarg(x_4);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_3, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_3);
x_17 = lean_nat_sub(x_3, lean_box(1));
x_18 = lean_array_fget(x_1, x_17);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_nat_add(x_3, x_19);
lean_dec(x_3);
x_21 = lean_array_push(x_4, x_18);
x_22 = lean_array_push(x_21, x_7);
x_3 = x_20;
x_4 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_unsigned_to_nat(2u);
x_25 = lean_nat_add(x_3, x_24);
lean_dec(x_3);
x_26 = lean_array_push(x_4, x_7);
x_3 = x_25;
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
x_5 = l___private_Init_LeanInit_14__filterSepElemsMAux___main___at_Array_filterSepElems___spec__2(x_1, x_2, x_3, x_4);
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
lean_object* l___private_Init_LeanInit_14__filterSepElemsMAux___main___at_Array_filterSepElems___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_LeanInit_14__filterSepElemsMAux___main___at_Array_filterSepElems___spec__2(x_1, x_2, x_3, x_4);
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
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = lean_array_push(x_2, x_6);
x_10 = l___private_Init_LeanInit_15__mapSepElemsMAux___main___rarg(x_3, x_4, x_5, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_11 = lean_array_fget(x_2, x_4);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_mod(x_4, x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_13);
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_4, x_17);
lean_dec(x_4);
x_19 = lean_array_push(x_5, x_11);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_3);
x_22 = lean_apply_1(x_3, x_11);
x_23 = lean_alloc_closure((void*)(l___private_Init_LeanInit_15__mapSepElemsMAux___main___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_23, 0, x_4);
lean_closure_set(x_23, 1, x_5);
lean_closure_set(x_23, 2, x_1);
lean_closure_set(x_23, 3, x_2);
lean_closure_set(x_23, 4, x_3);
x_24 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_22, x_23);
return x_24;
}
}
}
}
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_15__mapSepElemsMAux___main___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_LeanInit_15__mapSepElemsMAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_LeanInit_15__mapSepElemsMAux___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_LeanInit_15__mapSepElemsMAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_15__mapSepElemsMAux___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_LeanInit_15__mapSepElemsMAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_mapSepElemsM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_empty___closed__1;
x_6 = l___private_Init_LeanInit_15__mapSepElemsMAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
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
lean_object* l_Array_mapSepElemsM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_mapSepElemsM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___at_Array_mapSepElems___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_mod(x_3, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
x_12 = l_coeDecidableEq(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_15 = lean_array_push(x_4, x_7);
x_3 = x_14;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_2);
x_17 = lean_apply_1(x_2, x_7);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_20 = lean_array_push(x_4, x_17);
x_3 = x_19;
x_4 = x_20;
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
x_5 = l___private_Init_LeanInit_15__mapSepElemsMAux___main___at_Array_mapSepElems___spec__2(x_1, x_2, x_3, x_4);
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
lean_object* l___private_Init_LeanInit_15__mapSepElemsMAux___main___at_Array_mapSepElems___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_LeanInit_15__mapSepElemsMAux___main___at_Array_mapSepElems___spec__2(x_1, x_2, x_3, x_4);
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
lean_object* initialize_Init_Data_String_Basic(lean_object*);
lean_object* initialize_Init_Data_Array_Basic(lean_object*);
lean_object* initialize_Init_Data_UInt(lean_object*);
lean_object* initialize_Init_Data_Hashable(lean_object*);
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Control_Except(lean_object*);
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
res = initialize_Init_Control_Except(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_idBeginEscape = _init_l_Lean_idBeginEscape();
l_Lean_idEndEscape = _init_l_Lean_idEndEscape();
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
l_Lean_identKind___closed__1 = _init_l_Lean_identKind___closed__1();
lean_mark_persistent(l_Lean_identKind___closed__1);
l_Lean_identKind___closed__2 = _init_l_Lean_identKind___closed__2();
lean_mark_persistent(l_Lean_identKind___closed__2);
l_Lean_identKind = _init_l_Lean_identKind();
lean_mark_persistent(l_Lean_identKind);
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
l_Lean_nameLitKind___closed__1 = _init_l_Lean_nameLitKind___closed__1();
lean_mark_persistent(l_Lean_nameLitKind___closed__1);
l_Lean_nameLitKind___closed__2 = _init_l_Lean_nameLitKind___closed__2();
lean_mark_persistent(l_Lean_nameLitKind___closed__2);
l_Lean_nameLitKind = _init_l_Lean_nameLitKind();
lean_mark_persistent(l_Lean_nameLitKind);
l_Lean_fieldIdxKind___closed__1 = _init_l_Lean_fieldIdxKind___closed__1();
lean_mark_persistent(l_Lean_fieldIdxKind___closed__1);
l_Lean_fieldIdxKind___closed__2 = _init_l_Lean_fieldIdxKind___closed__2();
lean_mark_persistent(l_Lean_fieldIdxKind___closed__2);
l_Lean_fieldIdxKind = _init_l_Lean_fieldIdxKind();
lean_mark_persistent(l_Lean_fieldIdxKind);
l_Lean_Syntax_getKind___closed__1 = _init_l_Lean_Syntax_getKind___closed__1();
lean_mark_persistent(l_Lean_Syntax_getKind___closed__1);
l_Lean_Syntax_getKind___closed__2 = _init_l_Lean_Syntax_getKind___closed__2();
lean_mark_persistent(l_Lean_Syntax_getKind___closed__2);
l_Lean_reservedMacroScope = _init_l_Lean_reservedMacroScope();
lean_mark_persistent(l_Lean_reservedMacroScope);
l_Lean_firstFrontendMacroScope___closed__1 = _init_l_Lean_firstFrontendMacroScope___closed__1();
lean_mark_persistent(l_Lean_firstFrontendMacroScope___closed__1);
l_Lean_firstFrontendMacroScope = _init_l_Lean_firstFrontendMacroScope();
lean_mark_persistent(l_Lean_firstFrontendMacroScope);
l_Lean_Name_hasMacroScopes___main___closed__1 = _init_l_Lean_Name_hasMacroScopes___main___closed__1();
lean_mark_persistent(l_Lean_Name_hasMacroScopes___main___closed__1);
l___private_Init_LeanInit_1__eraseMacroScopesAux___main___closed__1 = _init_l___private_Init_LeanInit_1__eraseMacroScopesAux___main___closed__1();
lean_mark_persistent(l___private_Init_LeanInit_1__eraseMacroScopesAux___main___closed__1);
l_Lean_MacroScopesView_inhabited___closed__1 = _init_l_Lean_MacroScopesView_inhabited___closed__1();
lean_mark_persistent(l_Lean_MacroScopesView_inhabited___closed__1);
l_Lean_MacroScopesView_inhabited = _init_l_Lean_MacroScopesView_inhabited();
lean_mark_persistent(l_Lean_MacroScopesView_inhabited);
l_Lean_Macro_throwUnsupported___closed__1 = _init_l_Lean_Macro_throwUnsupported___closed__1();
lean_mark_persistent(l_Lean_Macro_throwUnsupported___closed__1);
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
