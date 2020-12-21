// Lean compiler output
// Module: Lean.Parser.Basic
// Imports: Init Lean.Data.Trie Lean.Data.Position Lean.Syntax Lean.ToExpr Lean.Environment Lean.Attributes Lean.Message Lean.Compiler.InitAttr Lean.ResolveName
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
lean_object* l_Lean_Parser_nonReservedSymbol___boxed(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_Parser_identEq(lean_object*);
lean_object* l_Lean_Parser_mergeOrElseErrors_match__1(lean_object*);
lean_object* l_Lean_Syntax_foldArgs___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParserOfStack___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeRevM_x3f_find___at___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Parser_info___default___elambda__1(lean_object*);
lean_object* l_Lean_Parser_finishCommentBlock(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_match__1(lean_object*);
lean_object* l_Lean_Parser_instInhabitedError;
lean_object* l_Lean_Parser_andthenInfo___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__4;
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l_Lean_Syntax_forArgsM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserInfo_firstTokens___default;
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__1;
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError_match__1___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Parser_checkTailWs(lean_object*);
extern lean_object* l_Lean_scientificLitKind___closed__1;
lean_object* l_Lean_Parser_identFn___closed__1;
lean_object* l_Lean_Parser_nodeWithAntiquot___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_prattParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedString;
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_decimalNumberFn_parseOptDot(lean_object*, lean_object*);
lean_object* l_Lean_Parser_evalParserConstUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___closed__1;
lean_object* l_Lean_Parser_strLitNoAntiquot___closed__2;
lean_object* l_Lean_Parser_errorAtSavedPosFn_match__1___rarg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Parser_sepByInfo(lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Parser_info___default;
lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_indexed_match__2(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Parser_eoi___closed__2;
lean_object* l_Lean_Parser_eoi___closed__1;
lean_object* l_Lean_Parser_parserOfStack___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_manyNoAntiquot(lean_object*);
lean_object* l_Lean_Parser_decimalNumberFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedByFn___closed__1;
extern lean_object* l_Lean_Syntax_mkAntiquotNode___closed__12;
lean_object* l_Lean_Parser_ParserState_keepNewError_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_toOptional_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Parser_Parser_info___default___closed__3;
extern lean_object* l_term_x5b___x5d___closed__9;
lean_object* l_Lean_Parser_leadPrec;
lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Char_quote___closed__1;
lean_object* l_Lean_Parser_strLitNoAntiquot;
lean_object* l_Lean_Parser_octalNumberFn___closed__1;
lean_object* l_Lean_Parser_quotedCharCoreFn(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind___closed__1;
lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_5915__match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_toOptional_match__1(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_fieldIdxKind___closed__2;
lean_object* l_Lean_Parser_checkTailWs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Parser_eoi;
extern uint32_t l_Lean_idBeginEscape;
lean_object* l_Lean_Parser_ParserState_errorMsg___default;
lean_object* l_Lean_Parser_optionaInfo___elambda__2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_binNumberFn___closed__1;
lean_object* l_Lean_Parser_hexNumberFn___closed__1;
lean_object* l_Lean_Parser_checkInsideQuotFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_binNumberFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_toErrorMsg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_merge_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__1;
lean_object* l_Lean_Parser_numberFnAux(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutInfo(lean_object*);
lean_object* l_Lean_Parser_mkAntiquotSplice(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_identEqFn___closed__1;
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_lookahead(lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__2(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t);
extern lean_object* l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
lean_object* l_Lean_Parser_hexNumberFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserOfStackFnUnsafe_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2(lean_object*);
lean_object* l_Lean_Parser_longestMatchFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_fieldIdx___closed__6;
lean_object* l_Lean_Parser_errorAtSavedPos___closed__1;
lean_object* l_Lean_Parser_nameLitNoAntiquot;
lean_object* l_Lean_Parser_nonReservedSymbolFnAux_match__1(lean_object*);
lean_object* l_Lean_Parser_ParserState_mkNode_match__1(lean_object*);
lean_object* l_Lean_Parser_ParserInfo_collectKinds___default___boxed(lean_object*);
lean_object* l_Lean_Parser_ParserState_keepLatest_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_nameLitNoAntiquot___closed__2;
lean_object* l_Lean_Parser_whitespace___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_instInhabitedError___closed__1;
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_mkTokenAndFixPos___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_matchPrefix___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_octalNumberFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object*);
lean_object* l_Lean_Parser_errorAtSavedPos___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_octalNumberFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_octalNumberFn___closed__2;
lean_object* l_Lean_Parser_hexNumberFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLitFnAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6172____lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_next(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_setExpected___elambda__1___boxed(lean_object*);
extern lean_object* l_term___u2218_____closed__6;
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkTrailingResult(lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParserFnRef;
lean_object* l_Lean_Parser_Error_expected___default;
lean_object* l_Lean_Parser_pushNone;
lean_object* l_Lean_Parser_checkNoImmediateColon___closed__1;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Parser_info___default___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_longestMatchFn_match__1(lean_object*);
uint8_t l_Lean_Parser_ParserContext_suppressInsideQuot___default;
lean_object* l_Lean_Parser_ParserInfo_collectKinds___default(lean_object*);
lean_object* l_Lean_Parser_mkTokenAndFixPos_match__1(lean_object*);
size_t l_USize_sub(size_t, size_t);
lean_object* l_Lean_Parser_PrattParsingTables_leadingTable___default;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot___closed__17;
lean_object* l_Lean_Parser_parserOfStackFnUnsafe_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbolInfo___closed__2;
lean_object* l_Lean_Parser_anyOfFn_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strAux_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isLitKind(lean_object*);
lean_object* l_Lean_Parser_atomicFn_match__1(lean_object*);
extern lean_object* l_Lean_fieldIdxKind___closed__1;
lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__1;
lean_object* l_Lean_Parser_withAntiquotFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParserOfStackFn___closed__2;
lean_object* l_Lean_Parser_longestMatchFnAux_parse_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGe(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbolFn(lean_object*, lean_object*, lean_object*);
uint8_t l_Char_isDigit(uint32_t);
lean_object* l_Lean_Parser_instCoeStringParser___boxed(lean_object*);
lean_object* l_Lean_Parser_evalParserConstUnsafe___closed__4;
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_Array_qpartition_loop___at_Lean_Parser_Error_toString___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_binNumberFn___lambda__1(uint32_t);
lean_object* l_Lean_Parser_FirstTokens_toStr_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_instInhabitedParserInfo___closed__1;
lean_object* l_Lean_Parser_nameLitNoAntiquot___closed__1;
lean_object* l_Lean_Parser_ParserState_mergeErrors_match__1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Parser_hexNumberFn___lambda__1(uint32_t);
lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkTokenAndFixPos___closed__2;
lean_object* l_IO_mkRef___at_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6172____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot___closed__9;
uint8_t l_Lean_Parser_octalNumberFn___lambda__1(uint32_t);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isIdRest___boxed(lean_object*);
lean_object* l_Lean_Parser_pushNone___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_notFollowedByFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelseFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4(lean_object*);
lean_object* l_Lean_Parser_ParserInfo_collectTokens___default___boxed(lean_object*);
lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot___closed__4;
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawCh___elambda__1(uint32_t, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
extern lean_object* l_Lean_charLitKind___closed__1;
lean_object* l_Lean_Parser_mkTokenAndFixPos_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGeFn_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_mkTokenAndFixPos___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutForbidden___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAtomicInfo(lean_object*);
lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Parser_info___default___closed__1;
uint8_t l_Char_isWhitespace(uint32_t);
lean_object* l_Lean_Parser_Error_merge_match__1(lean_object*);
lean_object* l_Lean_Parser_atomicFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_instBEqError___closed__1;
lean_object* l_Lean_Parser_instInhabitedParserFn___boxed(lean_object*);
lean_object* l_Lean_Parser_withPosition(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot___closed__11;
lean_object* l_Lean_Parser_indexed_match__7(lean_object*);
lean_object* l_Lean_Parser_evalParserConstUnsafe_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateCache_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Applicative_seqRight___default___rarg___closed__1;
lean_object* l_Lean_Parser_charLitFnAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_seq_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkPrecFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingParserAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkNodeToken(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_unexpected___default;
lean_object* l_Lean_Parser_tryAnti___boxed(lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Parser_symbolInfo___elambda__1(lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol(lean_object*, uint8_t);
lean_object* l_Lean_Parser_symbolFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkNodeToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkPrecFn___closed__1;
lean_object* l_Lean_Parser_TokenCacheEntry_startPos___default;
lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux_match__1(lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkStackTopFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_5915____boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_indexed_match__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_binNumberFn___closed__2;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_Parser_instInhabitedParserInfo___closed__3;
lean_object* l_Lean_Parser_nameLitFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_setExpected___elambda__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__2___boxed(lean_object*);
extern lean_object* l_term___x24_______closed__5;
lean_object* l_Lean_Parser_strLitFnAux___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nameLitKind;
lean_object* l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1;
lean_object* l_Lean_Parser_indexed_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_suppressInsideQuotFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_instInhabitedParser___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_foldArgsM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_fieldIdx___closed__4;
lean_object* l_Lean_Parser_instInhabitedParserInfo;
lean_object* l_Lean_Parser_mkAntiquotSplice___closed__2;
uint8_t l_Lean_Parser_ParserContext_insideQuot___default;
lean_object* l_Lean_Parser_checkPrecFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelseFnCore_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Parser_indexed___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6(lean_object*);
uint32_t l_Lean_Parser_getNext(lean_object*, lean_object*);
lean_object* l_List_toStringAux___at_Lean_Parser_FirstTokens_toStr___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenInfo___elambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot___closed__3;
lean_object* l_Lean_Parser_many1Fn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_satisfyFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserOfStackFnUnsafe_match__2(lean_object*);
lean_object* l_Lean_Parser_identEqFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Lean_Parser_indexed_match__5___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_antiquotExpr___closed__2;
lean_object* l_Lean_Parser_ParserState_keepLatest_match__1(lean_object*);
lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__3;
lean_object* l_Lean_Parser_instInhabitedParserCategory;
lean_object* l_Lean_Parser_ParserState_mkErrorsAt_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_scientificLitFn___closed__1;
lean_object* l_Lean_Parser_setExpectedFn_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawIdentFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquotSplice___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_whitespace___closed__1;
lean_object* l_Lean_Parser_scientificLitNoAntiquot___closed__3;
lean_object* l_Lean_Parser_indexed(lean_object*);
lean_object* l_Lean_Parser_tryAnti_match__2(lean_object*);
lean_object* l_Lean_Parser_setExpectedFn___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_Parser_invalidLongestMatchParser(lean_object*);
lean_object* l_Lean_Parser_invalidLongestMatchParser___closed__1;
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape___boxed(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot___closed__5;
lean_object* l_Lean_Syntax_forArgsM(lean_object*);
lean_object* l_Lean_Parser_octalNumberFn___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot___closed__15;
lean_object* l_Lean_Parser_atomicFn_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_decimalNumberFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquotSplice___closed__4;
lean_object* l_Lean_Parser_takeWhileFn(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__2(lean_object*);
lean_object* l_Lean_Parser_checkOutsideQuot___closed__1;
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_initCacheForInput(lean_object*);
lean_object* l_Lean_Parser_evalParserConst___rarg___boxed(lean_object*);
lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__4;
lean_object* l_Lean_Parser_mkAntiquot___closed__18;
lean_object* l_Lean_Parser_mkIdResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_fieldIdx___closed__1;
lean_object* l_Lean_Parser_TokenMap_insert(lean_object*);
lean_object* l_Lean_Parser_setExpected___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbol(lean_object*, lean_object*);
lean_object* l_Lean_Parser_longestMatchFn___closed__1;
lean_object* l_Lean_Parser_checkColGtFn_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkStackTopFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_setBlack___rarg(lean_object*);
lean_object* l_Lean_Parser_takeWhileFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquotSuffixSplice(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__1(lean_object*);
lean_object* l_Lean_Parser_identNoAntiquot___closed__1;
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbolFnAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1NoAntiquot___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_antiquotExpr___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_longestMatchStep_match__1(lean_object*);
lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3(lean_object*);
lean_object* l_Lean_Parser_mkTokenAndFixPos___closed__1;
lean_object* l_Lean_Parser_whitespace___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_errorAtSavedPosFn_match__2(lean_object*);
lean_object* l_Lean_Parser_mkTokenAndFixPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_quotedCharFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkNoWsBeforeFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAtomicInfo___elambda__2(lean_object*);
lean_object* l_Lean_Parser_strLitFn___closed__1;
lean_object* l_Lean_Parser_Error_instToStringError;
lean_object* l_Lean_Parser_orelseFnCore_match__1(lean_object*);
lean_object* l_Lean_Parser_ParserState_keepPrevError_match__1(lean_object*);
lean_object* l_Lean_Parser_evalParserConst___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_instToStringFirstTokens___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkErrorAt_match__1(lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByElemParser(lean_object*, lean_object*);
lean_object* l_Lean_Parser_indexed_match__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___boxed(lean_object*);
lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__6;
lean_object* l_Lean_Parser_checkTailWs_match__1(lean_object*);
lean_object* l_Lean_Parser_takeUntilFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_longestMatchFnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_lookaheadFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withResultOfInfo___elambda__2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawIdentNoAntiquot___closed__1;
lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_insertAux___rarg___closed__3;
lean_object* l_Lean_Parser_symbolFn___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l_Lean_Parser_numLitNoAntiquot___closed__1;
lean_object* l_Lean_Parser_indexed_match__4(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Parser_setExpected(lean_object*, lean_object*);
lean_object* l_Lean_Parser_longestMatchFnAux_parse_match__1(lean_object*);
lean_object* l_Lean_Parser_ParserState_keepLatest(lean_object*, lean_object*);
lean_object* l_Lean_Parser_instCoeStringParser(lean_object*);
lean_object* l_Lean_Parser_mkAntiquotSplice___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_antiquotNestedExpr___closed__1;
lean_object* l_Lean_Parser_checkNoWsBefore(lean_object*);
uint8_t l_List_beq___at_Lean_Syntax_structEq___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Parser_antiquotNestedExpr___closed__2;
lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object*);
lean_object* l_Lean_Parser_longestMatchFn_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind;
lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object*, uint8_t);
lean_object* l_Lean_Parser_runLongestMatchParser_match__1(lean_object*);
lean_object* l_Lean_Parser_parserOfStackFnUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_finishCommentBlock___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkNoWsBefore___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_foldArgs(lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__1(lean_object*);
lean_object* l_Lean_Parser_nodeInfo___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_merge(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserContext_resolveName(lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingParserAux_match__1(lean_object*);
lean_object* l_Lean_Parser_checkWsBeforeFn(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__3;
lean_object* l_Lean_Parser_ParserState_keepLatest___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_skip___closed__1;
lean_object* l_Lean_Syntax_foldArgsM(lean_object*, lean_object*);
extern lean_object* l_instReprList___rarg___closed__1;
lean_object* l_Lean_Parser_numLitNoAntiquot___closed__2;
uint8_t l_Lean_Parser_whitespace___lambda__1(uint32_t);
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
lean_object* l_Lean_Parser_antiquotNestedExpr___closed__8;
extern lean_object* l_stx___x3f___closed__3;
lean_object* l_Lean_Parser_fieldIdx___closed__3;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_Error_beq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_keepNewError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_antiquotExpr;
lean_object* l_Lean_Parser_instInhabitedParserCategory___closed__1;
lean_object* l_Lean_Parser_symbol(lean_object*);
lean_object* l_Lean_Parser_isQuotableCharDefault___boxed(lean_object*);
lean_object* l_Lean_Parser_checkLineEqFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5(lean_object*);
lean_object* l_Lean_Parser_symbolInfo___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_indexed_match__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_foldArgsM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_numLitFn(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(lean_object*, lean_object*);
uint8_t l_Lean_Parser_tryAnti(lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind___closed__1;
lean_object* l_Lean_Parser_optionaInfo(lean_object*);
lean_object* l_Lean_Parser_FirstTokens_seq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserOfStackFnUnsafe___closed__4;
lean_object* l_Lean_Parser_ParserState_mkNode_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_peekToken(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_toString___closed__4;
lean_object* l_Lean_Parser_SyntaxNodeKindSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind___closed__1;
lean_object* l_Lean_Parser_atomic(lean_object*);
lean_object* l_Lean_Parser_nodeWithAntiquot___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_antiquotNestedExpr___closed__4;
lean_object* l_Lean_Parser_checkColGeFn_match__1(lean_object*);
lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserOfStack___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_skip;
lean_object* l_Lean_Parser_mkAntiquotSplice___closed__3;
lean_object* l_Lean_Parser_binNumberFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_charLitNoAntiquot___closed__3;
lean_object* l_Lean_Parser_peekTokenAux(lean_object*, lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbolInfo___closed__3;
lean_object* l_Lean_Parser_sepByElemParser___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkOutsideQuot___closed__2;
lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_checkTailNoWs(lean_object*);
lean_object* l_Lean_Parser_checkTailWs___boxed(lean_object*);
lean_object* l_Lean_Parser_longestMatchFnAux_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_charLitFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_trailingLoopStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByElemParser___closed__1;
lean_object* l_Lean_Parser_charLitNoAntiquot___closed__2;
lean_object* l_Lean_Parser_longestMatchStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_instAndThenParser;
lean_object* l_Lean_Parser_tryAnti_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_setExpectedFn(lean_object*);
lean_object* l_List_eraseRepsAux___at_Lean_Parser_Error_toString___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLitFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot___closed__12;
lean_object* l_Lean_Parser_ParserState_mkErrorAt_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_0__mkPanicMessage___closed__2;
lean_object* l_Lean_Parser_FirstTokens_seq_match__1(lean_object*);
lean_object* l_Lean_Parser_ParserContext_savedPos_x3f___default;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6172____lambda__1(lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_Parser_instInhabitedInputContext;
lean_object* l_Lean_Parser_errorAtSavedPosFn(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_antiquotNestedExpr___closed__7;
lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object*);
lean_object* l_Lean_Parser_antiquotExpr___closed__1;
lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__5;
lean_object* l_Lean_Parser_categoryParserOfStack(lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkWsBefore(lean_object*);
lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_setCache(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkErrorsAt_match__1(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot___closed__10;
lean_object* l_Lean_Parser_indexed_match__6(lean_object*);
lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_antiquotNestedExpr___closed__5;
lean_object* l_Lean_Parser_mkIdResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLitNoAntiquot___closed__1;
lean_object* l_Lean_Parser_sepByFn(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_fieldIdx___closed__2;
lean_object* l_Lean_Parser_many1Unbox___lambda__1(lean_object*);
lean_object* l_Lean_Parser_instBEqLeadingIdentBehavior;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1202____closed__1;
lean_object* l_Lean_Parser_rawCh___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_getNext___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
extern lean_object* l_Lean_charLitKind;
lean_object* l_Lean_Parser_errorFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_maxPrec;
lean_object* l_Lean_Parser_withForbidden___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mergeOrElseErrors_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserOfStackFnUnsafe___closed__3;
lean_object* l_Lean_Parser_checkLineEqFn_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6(lean_object*);
lean_object* l_Lean_Parser_FirstTokens_merge(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquotSplice___closed__1;
lean_object* l_Lean_Parser_many1Unbox___closed__1;
lean_object* l_Lean_Parser_setExpectedFn_match__1(lean_object*);
lean_object* l_Lean_Parser_sepBy___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_pushNone___elambda__1___rarg(lean_object*);
lean_object* l_Lean_Parser_scientificLitFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError_match__1(lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Lean_Parser_PrattParsingTables_leadingParsers___default;
lean_object* l_Lean_Parser_fieldIdx___closed__5;
lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt_match__1(lean_object*);
lean_object* l_Lean_Parser_symbolInfo___elambda__2(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGtFn_match__1(lean_object*);
lean_object* l_Lean_Parser_instInhabitedPrattParsingTables___closed__1;
lean_object* l_Lean_Parser_ParserState_mkEOIError___closed__1;
uint8_t l_Lean_Parser_isIdCont(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mergeOrElseErrors___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkNoImmediateColon___elambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken_match__1(lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_evalParserConst___rarg(lean_object*);
lean_object* l_Lean_Parser_TokenMap_instInhabitedTokenMap(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mergeErrors_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot___closed__13;
lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_errorAtSavedPosFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelseFnCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3(lean_object*);
lean_object* l_Lean_Parser_unicodeSymbol___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeInfo___elambda__2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserOfStack(lean_object*, lean_object*);
lean_object* l_Lean_Parser_identFnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_identFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strLitNoAntiquot___closed__3;
lean_object* l_Array_findSomeRevM_x3f_find___at___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserOfStackFnUnsafe___closed__5;
lean_object* l_Lean_Parser_charLitNoAntiquot___closed__1;
lean_object* l_Lean_Parser_mkAntiquotSplice___closed__5;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6190____lambda__1(lean_object*);
lean_object* l_Lean_Parser_identFnAux_parse___closed__2;
lean_object* l_Lean_Parser_evalInsideQuot___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkTailNoWs___boxed(lean_object*);
lean_object* l_Lean_Parser_takeUntilFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_epsilonInfo___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_checkOutsideQuot;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAtomicInfo___elambda__1(lean_object*);
lean_object* l_Lean_Parser_anyOfFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_evalParserConst(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkEmptySubstringAt(lean_object*, lean_object*);
lean_object* l_Lean_Parser_anyOfFn___closed__1;
lean_object* l_Lean_Parser_Error_toString___closed__2;
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* l_Lean_Parser_categoryParserOfStackFn_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkInsideQuot;
lean_object* l_Lean_Parser_identFnAux_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nameLitNoAntiquot___closed__3;
lean_object* l_Lean_Parser_leadingParserAux_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_longestMatchMkResult(lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg___boxed(lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_Lean_Parser_toggleInsideQuot(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
lean_object* l_Lean_Parser_identFnAux_parse___closed__1;
lean_object* l_Lean_Parser_indexed_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_5915__match__1___rarg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawCh(uint32_t, uint8_t);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByInfo___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParserOfStackFn_match__1(lean_object*);
lean_object* l_Lean_Parser_quotedCharCoreFn___closed__1;
lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_antiquotNestedExpr___closed__3;
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(lean_object*);
lean_object* l_Lean_Parser_sepBy1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(uint32_t);
lean_object* l_Lean_Parser_binNumberFn___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_identFnAux_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object*);
lean_object* l_Lean_Parser_termParser(lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_manyAux(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Parser_checkInsideQuotFn___closed__1;
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot___closed__7;
lean_object* l_Lean_Parser_pushNone___closed__1;
lean_object* l_Lean_Parser_chFn(uint32_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_antiquotNestedExpr;
lean_object* l_Lean_Parser_mkAtomicInfo___elambda__2___boxed(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_all___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_trailingNodeAux(lean_object*, lean_object*);
lean_object* l_Lean_Parser_trailingNodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_instToStringFirstTokens;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString___closed__1;
lean_object* l_Lean_Parser_checkNoImmediateColon;
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_scientificLitNoAntiquot___closed__2;
lean_object* l_Lean_Parser_withResultOfFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutPosition___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__7;
lean_object* l_Lean_Parser_rawIdentNoAntiquot___closed__2;
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_runLongestMatchParser_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_anyOfFn_match__1(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot___elambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkOutsideQuotFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserOfStackFnUnsafe_match__1(lean_object*);
lean_object* l_Lean_Parser_sepBy___elambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParserFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_keepPrevError_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkInsideQuot___closed__1;
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateCache(lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1Unbox___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_instInhabitedParser___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6190____closed__1;
lean_object* l_Lean_Parser_sepBy1Info(lean_object*, lean_object*);
lean_object* l_Lean_Parser_quotedCharFn___closed__1;
lean_object* l_Lean_Parser_charLitFnAux___closed__1;
lean_object* l_Lean_Parser_hexDigitFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkInsideQuotFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mergeErrors___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString(lean_object*);
lean_object* l_Lean_Parser_instOrElseParser___closed__1;
lean_object* l_Lean_Parser_trailingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_scientificLitNoAntiquot___closed__1;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelseInfo___elambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkInsideQuot___closed__2;
lean_object* l_Lean_Parser_pushNone___closed__2;
lean_object* l_Lean_Parser_suppressInsideQuot(lean_object*);
lean_object* l_Lean_Parser_quotedCharFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_longestMatchFnAux_parse_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12721____closed__9;
lean_object* l_Lean_Parser_checkTailNoWs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_noFirstTokenInfo___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_indexed_match__7___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Parser_info___default___closed__2;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__1(lean_object*);
lean_object* l_Lean_Parser_checkColGeFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_charLitFnAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_prattParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_evalParserConstUnsafe___closed__3;
lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_ParserState_mkTrailingNode_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_identKind;
lean_object* l_Lean_Parser_satisfySymbolFn_match__1(lean_object*);
lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_fieldIdxFn___closed__1;
lean_object* l_Lean_Parser_withForbidden(lean_object*, lean_object*);
lean_object* l_Lean_Parser_trailingLoop(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol___boxed(lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_Parser_toggleInsideQuotFn(lean_object*, lean_object*, lean_object*);
extern lean_object* l_term_x5b___x5d___closed__5;
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_toStr_match__1(lean_object*);
lean_object* l_Lean_Parser_hexDigitFn(lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot___closed__16;
lean_object* l_Lean_Parser_checkNoImmediateColon___elambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkLineEq(lean_object*);
lean_object* l_Lean_Parser_scientificLitNoAntiquot;
lean_object* l_Lean_Parser_trailingLoop_match__1(lean_object*);
lean_object* l_Lean_Syntax_forArgsM___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserOfStackFn___rarg(lean_object*);
lean_object* l_Lean_Parser_instInhabitedInputContext___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Parser_Error_toString(lean_object*);
lean_object* l_Lean_Parser_categoryParserOfStackFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkNoImmediateColon___elambda__1___closed__1;
lean_object* l_Lean_Parser_runLongestMatchParser(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkTrailingNode___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquotSplice___closed__6;
lean_object* l_Lean_Parser_FirstTokens_merge_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Parser_Error_instBEqError;
extern lean_object* l_Lean_scientificLitKind;
lean_object* l_Lean_Parser_ParserState_keepNewError___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByNoAntiquot___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_PrattParsingTables_trailingTable___default;
lean_object* l_Lean_Parser_ParserModuleContext_currNamespace___default;
lean_object* l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1(lean_object*);
lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1(lean_object*);
lean_object* l_Lean_Parser_withPosition___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_numLitNoAntiquot___closed__3;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6172____closed__1;
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Parser_info___default___elambda__2___boxed(lean_object*);
uint8_t l_Std_RBNode_isRed___rarg(lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError_match__1(lean_object*);
lean_object* l_Lean_Parser_antiquotNestedExpr___closed__6;
lean_object* l_Lean_Parser_TokenMap_insert_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1NoAntiquot(lean_object*);
lean_object* l_Lean_Parser_TokenCacheEntry_token___default;
lean_object* l_Lean_Parser_ParserState_toErrorMsg_match__1(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_Parser_chFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_numLitNoAntiquot;
lean_object* l_Lean_Parser_Error_instToStringError___closed__1;
lean_object* l_Lean_Parser_checkTailNoWs_match__1(lean_object*);
lean_object* l_Lean_Parser_Error_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_TokenMap_instEmptyCollectionTokenMap(lean_object*);
lean_object* l_Lean_Parser_orelseInfo___elambda__1(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_5915_(uint8_t, uint8_t);
lean_object* l_Lean_Parser_errorAtSavedPos(lean_object*, uint8_t);
lean_object* l_Lean_Parser_mkAntiquot___closed__14;
lean_object* l_Lean_Parser_FirstTokens_toStr___closed__1;
lean_object* l_Lean_Parser_withoutInfo___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_setExpectedFn___boxed(lean_object*);
lean_object* l_Lean_Parser_ParserModuleContext_openDecls___default;
lean_object* l_Lean_Parser_withResultOf(lean_object*, lean_object*);
extern lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_satisfySymbolFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbolInfo(lean_object*);
lean_object* l_Lean_Parser_checkStackTop(lean_object*, lean_object*);
lean_object* l_String_decLt___boxed(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_instInhabitedPrattParsingTables;
lean_object* l_Lean_Parser_eoiFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1Fn(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelseFnCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_epsilonInfo;
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__3(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1(lean_object*);
extern lean_object* l_Lean_Syntax_mkAntiquotNode___closed__2;
lean_object* l_Lean_Parser_epsilonInfo___closed__3;
lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__2___boxed(lean_object*);
lean_object* l_Lean_Parser_instInhabitedParser;
lean_object* l_Lean_Parser_categoryParser___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_pushNone___elambda__1(lean_object*);
lean_object* l_Lean_Parser_tryAnti_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_toStr___closed__2;
lean_object* l_Lean_Parser_rawIdentNoAntiquot;
lean_object* l_Lean_Parser_ParserState_replaceLongest(lean_object*, lean_object*);
lean_object* l_Lean_Parser_indexed_match__5(lean_object*);
lean_object* l_Lean_Parser_fieldIdxFn___boxed(lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_UInt32_decEq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_decimalNumberFn_parseOptDot___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolFn___closed__1;
lean_object* l_Lean_Parser_ParserContext_forbiddenTk_x3f___default;
lean_object* l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5(lean_object*);
lean_object* l_Lean_Parser_checkNoWsBefore___elambda__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap___closed__1;
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_PrattParsingTables_trailingParsers___default;
lean_object* l_Lean_Parser_noFirstTokenInfo___elambda__2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutPosition(lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_instInhabitedFirstTokens;
lean_object* l_Lean_Parser_epsilonInfo___closed__2;
lean_object* l_Lean_Parser_rawCh___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_numberFnAux___closed__1;
lean_object* l_Lean_Parser_nonReservedSymbolInfo___closed__1;
lean_object* l_Lean_Parser_instAndThenParser___closed__1;
lean_object* l_List_eraseReps___at_Lean_Parser_Error_toString___spec__3(lean_object*);
lean_object* l_Lean_Parser_instInhabitedParser___closed__2;
lean_object* l_Std_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_isIdCont___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Parser_takeWhile1Fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_identNoAntiquot___closed__3;
lean_object* l_Lean_Parser_epsilonInfo___closed__1;
lean_object* l_Lean_Parser_checkPrec(lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_5915__match__1(lean_object*);
lean_object* l_Lean_Parser_checkNoImmediateColon___closed__2;
lean_object* l_Lean_Parser_identEqFn_match__1(lean_object*);
lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_instInhabitedParserFn___rarg(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_Parser_rawIdentFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Parser_info___default___elambda__2(lean_object*);
lean_object* l_String_trim(lean_object*);
lean_object* l_Lean_isIdEndEscape___boxed(lean_object*);
lean_object* l_Lean_Parser_parserOfStackFnUnsafe___closed__2;
lean_object* l_Lean_Parser_leadingParserAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawFn(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_charLitFn___closed__1;
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* l_Lean_Parser_instInhabitedParserInfo___closed__2;
lean_object* l_Lean_Parser_errorAtSavedPosFn_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_pos___default;
lean_object* l_Lean_Parser_checkWsBeforeFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_optionalFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nameLitFn___closed__1;
lean_object* l_Lean_Parser_checkOutsideQuotFn___closed__1;
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkOutsideQuotFn___boxed(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Parser_TokenMap_insert___rarg(lean_object*, lean_object*, lean_object*);
extern size_t l_Std_PersistentHashMap_insertAux___rarg___closed__2;
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strAux_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_evalParserConstUnsafe___closed__2;
uint8_t l_Lean_isIdFirst(uint32_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeWhile1Fn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_instInhabitedParserFn___rarg___boxed(lean_object*);
lean_object* l_Lean_Parser_errorFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_identEqFn_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_many1Unbox(lean_object*);
lean_object* l_Lean_Parser_parserOfStackFnUnsafe___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByInfo___elambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGt(lean_object*);
lean_object* l_Lean_Parser_symbolInfo___closed__1;
extern lean_object* l_prec_x28___x29___closed__7;
lean_object* l_Lean_Parser_indexed_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux_match__1(lean_object*);
extern lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f_match__1___rarg___closed__1;
lean_object* l_Lean_Parser_mkAntiquot___closed__6;
lean_object* l_Lean_Parser_parserOfStackFnUnsafe___closed__1;
extern lean_object* l_Lean_Syntax_mkAntiquotNode___closed__6;
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6190_(lean_object*);
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6172_(lean_object*);
uint8_t l_Lean_Parser_instInhabitedLeadingIdentBehavior;
lean_object* l_Lean_Parser_fieldIdx___closed__7;
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_instBEqLeadingIdentBehavior___closed__1;
lean_object* l_Lean_Parser_optionaInfo___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp(lean_object*, lean_object*);
lean_object* l_Lean_Parser_identFnAux_parse___closed__3;
lean_object* l_Lean_Parser_ParserState_mkTrailingNode_match__1(lean_object*);
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__2(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_prec_x28___x29___closed__3;
lean_object* l_Lean_Parser_ParserInfo_collectTokens___default(lean_object*);
lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_evalParserConstUnsafe___closed__1;
lean_object* l_Lean_Parser_eoiFn___closed__1;
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7(lean_object*);
lean_object* l_Lean_Parser_mkAtomicInfo___closed__1;
lean_object* l_Lean_Parser_checkColGtFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_toString___closed__3;
lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
lean_object* l_Lean_Parser_TokenMap_insert_match__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_fieldIdx;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserOfStackFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParserOfStackFn___closed__1;
lean_object* l_Lean_Parser_manyFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString_match__1(lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateCache_match__1(lean_object*);
lean_object* l_Lean_Parser_eoiFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_satisfySymbolFn_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1Info___elambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_epsilonInfo___elambda__2(lean_object*);
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_epsilonInfo___elambda__1(lean_object*);
lean_object* l_Lean_Parser_categoryParserFnExtension;
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_epsilonInfo___elambda__2___boxed(lean_object*);
lean_object* l_Lean_Parser_withResultOfInfo___elambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
lean_object* l_Lean_Parser_node(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_keepNewError_match__1(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot___closed__8;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolInfo(lean_object*, lean_object*);
lean_object* l_Lean_Parser_identNoAntiquot;
lean_object* l_Lean_Parser_evalParserConstUnsafe_match__1(lean_object*);
extern lean_object* l_stx___x2a___closed__3;
lean_object* l_Lean_Parser_tryAnti_match__1(lean_object*);
lean_object* l_Lean_Parser_ParserState_keepPrevError___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_strAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_instInhabitedParserFn(lean_object*);
lean_object* l_Lean_Parser_mkAntiquotSplice___closed__7;
lean_object* l_Lean_Parser_instOrElseParser;
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Parser_instInhabitedParser___closed__1;
lean_object* l_Lean_Parser_mkTokenAndFixPos(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAtomicInfo___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object*);
lean_object* l_Lean_Parser_checkWsBefore___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*);
uint8_t l_UInt32_decLe(uint32_t, uint32_t);
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_trailingLoop_match__1___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Parser_ParserState_hasError(lean_object*);
lean_object* l_Lean_Parser_symbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_hexDigitFn___closed__1;
lean_object* l_Lean_Parser_mkAtom(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parserOfStackFn___rarg___boxed(lean_object*);
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*);
lean_object* l_Lean_Parser_checkLineEqFn_match__1(lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_Parser_indexed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParserOfStackFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_keepPrevError(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkWsBefore___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1___elambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_TokenCacheEntry_stopPos___default;
lean_object* l_Lean_Parser_setExpected___elambda__1(lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolInfo___closed__1;
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_foldArgs___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_hexNumberFn___lambda__1___boxed(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_replaceLongest___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_longestMatchStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_quotedCharCoreFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_toString___closed__1;
lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__1(lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot___closed__2;
lean_object* l_Lean_Parser_withResultOfInfo(lean_object*);
lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParserOfStack___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition_loop___at_Lean_Parser_Error_toString___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_manyAux___closed__1;
lean_object* l_Lean_Parser_identFn(lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_errorAtSavedPosFn_match__1(lean_object*);
lean_object* l_Lean_Parser_longestMatchFnAux_parse_match__2(lean_object*);
lean_object* l_Lean_Parser_antiquotExpr___closed__3;
lean_object* l_Lean_Parser_charLitNoAntiquot;
lean_object* l_Lean_Parser_FirstTokens_merge_match__1(lean_object*);
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_indexed_match__3(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1Info___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7(lean_object*);
lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2(lean_object*);
lean_object* l_Lean_Parser_mkAtomicInfo___closed__2;
lean_object* l_Lean_Parser_sepBy___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_identNoAntiquot___closed__2;
lean_object* l_Lean_Parser_withoutForbidden(lean_object*);
lean_object* l_Lean_Parser_indexed_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__2;
extern lean_object* l_term_x5b___x5d___closed__3;
lean_object* l_Lean_Parser_nonReservedSymbolInfo___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mergeErrors(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_numberFnAux___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1(lean_object*);
lean_object* l_Lean_Parser_fieldIdxFn(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_hexNumberFn___closed__2;
lean_object* l_Lean_Parser_mkIdent(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nameLitKind___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_evalInsideQuot(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_isLitKind___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_error(lean_object*);
lean_object* l_List_toStringAux___at_Lean_Parser_FirstTokens_toStr___spec__2(uint8_t, lean_object*);
lean_object* l_Lean_Parser_longestMatchStep_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Char_isDigit___boxed(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot___closed__1;
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_stxStack___default;
uint8_t l_Lean_Parser_isLitKind(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_strLitKind;
x_3 = lean_name_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_numLitKind;
x_5 = lean_name_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_charLitKind;
x_7 = lean_name_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_nameLitKind;
x_9 = lean_name_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_scientificLitKind;
x_11 = lean_name_eq(x_1, x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
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
}
lean_object* l_Lean_Parser_isLitKind___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_isLitKind(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_mkAtom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_mkIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
uint32_t l_Lean_Parser_getNext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; 
x_3 = lean_string_utf8_next(x_1, x_2);
x_4 = lean_string_utf8_get(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_getNext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_getNext(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_maxPrec() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1024u);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_leadPrec() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1023u);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_TokenCacheEntry_startPos___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_TokenCacheEntry_stopPos___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_TokenCacheEntry_token___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Lean_Parser_initCacheForInput(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_initCacheForInput(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__3(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_19 = l_Std_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2(x_6, x_16, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_18;
x_6 = x_19;
goto _start;
}
}
}
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_eq(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_name_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_name_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_Std_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_Std_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_52 = x_2 & x_51;
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(2);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_name_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_Std_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__4(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = x_85 <= x_3;
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_93 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__3(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__4(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = x_99 <= x_3;
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_107 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__3(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash(x_2);
x_8 = 1;
x_9 = l_Std_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Name_hash(x_2);
x_15 = 1;
x_16 = l_Std_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l_Lean_Parser_SyntaxNodeKindSet_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Std_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__3(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedParserDescr___closed__1;
x_2 = l_Lean_instInhabitedFileMap___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instInhabitedInputContext___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserModuleContext_currNamespace___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserModuleContext_openDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static uint8_t _init_l_Lean_Parser_ParserContext_insideQuot___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Parser_ParserContext_suppressInsideQuot___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserContext_savedPos_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserContext_forbiddenTk_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Lean_Parser_ParserContext_resolveName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_ResolveName_resolveGlobalName(x_4, x_5, x_6, x_2);
lean_dec(x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Error_unexpected___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedParserDescr___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Error_expected___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedError___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedError() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instInhabitedError___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_apply_2(x_4, x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_4);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_apply_2(x_5, x_15, x_8);
return x_16;
}
}
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString_match__1___rarg), 5, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" or ");
return x_1;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString___closed__1;
x_9 = lean_string_append(x_6, x_8);
x_10 = lean_string_append(x_9, x_7);
lean_dec(x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_term_x5b___x5d___closed__5;
x_13 = lean_string_append(x_11, x_12);
x_14 = l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString(x_3);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
return x_15;
}
}
}
}
}
lean_object* l_Array_qpartition_loop___at_Lean_Parser_Error_toString___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_String_instInhabitedString;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_1);
lean_inc(x_3);
x_12 = lean_apply_2(x_1, x_11, x_3);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_6 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_swap(x_4, x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
x_4 = x_17;
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
}
static lean_object* _init_l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_decLt___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_2, x_3);
if (x_13 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_14 = lean_nat_add(x_2, x_3);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_41 = l_String_instInhabitedString;
x_42 = lean_array_get(x_41, x_1, x_16);
x_43 = lean_array_get(x_41, x_1, x_2);
x_44 = lean_string_dec_lt(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_44 == 0)
{
x_17 = x_1;
goto block_40;
}
else
{
lean_object* x_45; 
x_45 = lean_array_swap(x_1, x_2, x_16);
x_17 = x_45;
goto block_40;
}
block_40:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = l_String_instInhabitedString;
x_19 = lean_array_get(x_18, x_17, x_3);
x_20 = lean_array_get(x_18, x_17, x_2);
x_21 = lean_string_dec_lt(x_19, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_array_get(x_18, x_17, x_16);
x_23 = lean_string_dec_lt(x_22, x_19);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_24 = l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___closed__1;
lean_inc_n(x_2, 2);
x_25 = l_Array_qpartition_loop___at_Lean_Parser_Error_toString___spec__2(x_24, x_3, x_19, x_17, x_2, x_2);
x_4 = x_25;
goto block_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
x_26 = lean_array_swap(x_17, x_16, x_3);
lean_dec(x_16);
x_27 = lean_array_get(x_18, x_26, x_3);
x_28 = l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___closed__1;
lean_inc_n(x_2, 2);
x_29 = l_Array_qpartition_loop___at_Lean_Parser_Error_toString___spec__2(x_28, x_3, x_27, x_26, x_2, x_2);
x_4 = x_29;
goto block_12;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_19);
x_30 = lean_array_swap(x_17, x_2, x_3);
x_31 = lean_array_get(x_18, x_30, x_16);
x_32 = lean_array_get(x_18, x_30, x_3);
x_33 = lean_string_dec_lt(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_16);
x_34 = l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___closed__1;
lean_inc_n(x_2, 2);
x_35 = l_Array_qpartition_loop___at_Lean_Parser_Error_toString___spec__2(x_34, x_3, x_32, x_30, x_2, x_2);
x_4 = x_35;
goto block_12;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_32);
x_36 = lean_array_swap(x_30, x_16, x_3);
lean_dec(x_16);
x_37 = lean_array_get(x_18, x_36, x_3);
x_38 = l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___closed__1;
lean_inc_n(x_2, 2);
x_39 = l_Array_qpartition_loop___at_Lean_Parser_Error_toString___spec__2(x_38, x_3, x_37, x_36, x_2, x_2);
x_4 = x_39;
goto block_12;
}
}
}
}
block_12:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_nat_dec_le(x_3, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1(x_6, x_2, x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_1 = x_8;
x_2 = x_10;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
}
}
lean_object* l_List_eraseRepsAux___at_Lean_Parser_Error_toString___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_string_dec_eq(x_1, x_7);
if (x_9 == 0)
{
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_1);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_2;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_free_object(x_2);
lean_dec(x_7);
x_2 = x_8;
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = lean_string_dec_eq(x_1, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_3);
x_1 = x_12;
x_2 = x_13;
x_3 = x_15;
goto _start;
}
else
{
lean_dec(x_12);
x_2 = x_13;
goto _start;
}
}
}
}
}
lean_object* l_List_eraseReps___at_Lean_Parser_Error_toString___spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = l_List_eraseRepsAux___at_Lean_Parser_Error_toString___spec__4(x_3, x_4, x_5);
return x_6;
}
}
}
static lean_object* _init_l_Lean_Parser_Error_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected ");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Error_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("; ");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Error_toString___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_List_append___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Error_toString___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Error_toString___closed__2;
x_2 = l_Lean_Parser_Error_toString___closed__3;
x_3 = l_String_intercalate(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Error_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_instInhabitedParserDescr___closed__1;
x_5 = lean_string_dec_eq(x_2, x_4);
x_6 = lean_box(0);
x_7 = l_List_beq___at_Lean_Syntax_structEq___spec__3(x_3, x_6);
if (x_5 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_6);
if (x_7 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = l_List_redLength___rarg(x_3);
x_10 = lean_mk_empty_array_with_capacity(x_9);
lean_dec(x_9);
x_11 = l_List_toArrayAux___rarg(x_3, x_10);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1(x_11, x_15, x_14);
lean_dec(x_14);
x_17 = lean_array_to_list(lean_box(0), x_16);
x_18 = l_List_eraseReps___at_Lean_Parser_Error_toString___spec__3(x_17);
x_19 = l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString(x_18);
x_20 = l_Lean_Parser_Error_toString___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
x_23 = l_List_append___rarg(x_8, x_22);
x_24 = l_Lean_Parser_Error_toString___closed__2;
x_25 = l_String_intercalate(x_24, x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
x_26 = l_List_append___rarg(x_8, x_6);
x_27 = l_Lean_Parser_Error_toString___closed__2;
x_28 = l_String_intercalate(x_27, x_26);
return x_28;
}
}
else
{
lean_dec(x_2);
if (x_7 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_29 = l_List_redLength___rarg(x_3);
x_30 = lean_mk_empty_array_with_capacity(x_29);
lean_dec(x_29);
x_31 = l_List_toArrayAux___rarg(x_3, x_30);
x_32 = lean_array_get_size(x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_sub(x_32, x_33);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1(x_31, x_35, x_34);
lean_dec(x_34);
x_37 = lean_array_to_list(lean_box(0), x_36);
x_38 = l_List_eraseReps___at_Lean_Parser_Error_toString___spec__3(x_37);
x_39 = l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString(x_38);
x_40 = l_Lean_Parser_Error_toString___closed__1;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_6);
x_43 = l_List_append___rarg(x_6, x_42);
x_44 = l_Lean_Parser_Error_toString___closed__2;
x_45 = l_String_intercalate(x_44, x_43);
return x_45;
}
else
{
lean_object* x_46; 
lean_dec(x_3);
x_46 = l_Lean_Parser_Error_toString___closed__4;
return x_46;
}
}
}
}
lean_object* l_Array_qpartition_loop___at_Lean_Parser_Error_toString___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qpartition_loop___at_Lean_Parser_Error_toString___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Error_instToStringError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Error_toString), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Error_instToStringError() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Error_instToStringError___closed__1;
return x_1;
}
}
uint8_t l_Lean_Parser_Error_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_string_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_List_beq___at_Lean_Syntax_structEq___spec__3(x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Parser_Error_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_Error_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Error_instBEqError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Error_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Error_instBEqError() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Error_instBEqError___closed__1;
return x_1;
}
}
lean_object* l_Lean_Parser_Error_merge_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Parser_Error_merge_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Error_merge_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_Error_merge(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_instInhabitedParserDescr___closed__1;
x_6 = lean_string_dec_eq(x_3, x_5);
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_List_append___rarg(x_9, x_4);
if (x_6 == 0)
{
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
else
{
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_10);
return x_1;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = l_List_append___rarg(x_12, x_4);
if (x_6 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
}
static lean_object* _init_l_Lean_Parser_ParserState_stxStack___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_pos___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_errorMsg___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_Lean_Parser_Error_beq(x_6, x_7);
return x_8;
}
}
}
}
uint8_t l_Lean_Parser_ParserState_hasError(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_box(0);
x_4 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
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
lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_ParserState_hasError(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_ParserState_stackSize(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ParserState_stackSize(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_ParserState_restore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 3);
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_dec(x_7);
x_8 = l_Array_shrink___rarg(x_5, x_2);
x_9 = lean_box(0);
lean_ctor_set(x_1, 3, x_9);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_Array_shrink___rarg(x_10, x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set(x_14, 3, x_13);
return x_14;
}
}
}
lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_restore(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_ParserState_setPos(lean_object* x_1, lean_object* x_2) {
_start:
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Parser_ParserState_setCache(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_2);
lean_ctor_set(x_8, 3, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_array_push(x_4, x_2);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_10 = lean_array_push(x_6, x_2);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_pop(x_3);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = lean_array_pop(x_5);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_8);
return x_10;
}
}
}
lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Array_shrink___rarg(x_4, x_2);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_10 = l_Array_shrink___rarg(x_6, x_2);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_shrinkStack(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_ParserState_next(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
x_6 = lean_string_utf8_next(x_2, x_3);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_10 = lean_string_utf8_next(x_2, x_3);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_next(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_ParserState_toErrorMsg_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_ParserState_toErrorMsg_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_ParserState_toErrorMsg_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = l_Lean_instInhabitedParserDescr___closed__1;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_FileMap_toPosition(x_7, x_8);
lean_dec(x_7);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Parser_Error_toString(x_5);
x_14 = l_Lean_mkErrorStringWithPos(x_10, x_11, x_12, x_13);
lean_dec(x_13);
return x_14;
}
}
}
lean_object* l_Lean_Parser_ParserState_mkNode_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_ParserState_mkNode_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_ParserState_mkNode_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_eq(x_10, x_3);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 0);
lean_dec(x_16);
lean_inc(x_3);
lean_inc(x_4);
x_17 = l_Array_extract___rarg(x_4, x_3, x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Array_shrink___rarg(x_4, x_3);
lean_dec(x_3);
x_20 = lean_array_push(x_19, x_18);
lean_ctor_set(x_1, 0, x_20);
return x_1;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_4);
x_21 = l_Array_extract___rarg(x_4, x_3, x_10);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Array_shrink___rarg(x_4, x_3);
lean_dec(x_3);
x_24 = lean_array_push(x_23, x_22);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set(x_25, 2, x_6);
lean_ctor_set(x_25, 3, x_7);
return x_25;
}
}
else
{
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_1);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_1, 3);
lean_dec(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_1, 0);
lean_dec(x_30);
x_31 = lean_array_get_size(x_4);
lean_inc(x_3);
lean_inc(x_4);
x_32 = l_Array_extract___rarg(x_4, x_3, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Array_shrink___rarg(x_4, x_3);
lean_dec(x_3);
x_35 = lean_array_push(x_34, x_33);
lean_ctor_set(x_1, 0, x_35);
return x_1;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_1);
x_36 = lean_array_get_size(x_4);
lean_inc(x_3);
lean_inc(x_4);
x_37 = l_Array_extract___rarg(x_4, x_3, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Array_shrink___rarg(x_4, x_3);
lean_dec(x_3);
x_40 = lean_array_push(x_39, x_38);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_5);
lean_ctor_set(x_41, 2, x_6);
lean_ctor_set(x_41, 3, x_7);
return x_41;
}
}
}
}
lean_object* l_Lean_Parser_ParserState_mkTrailingNode_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_ParserState_mkTrailingNode_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_ParserState_mkTrailingNode_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
x_8 = lean_array_get_size(x_5);
lean_inc(x_5);
x_9 = l_Array_extract___rarg(x_5, x_7, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Array_shrink___rarg(x_5, x_3);
x_12 = lean_array_push(x_11, x_10);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_3, x_17);
x_19 = lean_array_get_size(x_13);
lean_inc(x_13);
x_20 = l_Array_extract___rarg(x_13, x_18, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Array_shrink___rarg(x_13, x_3);
x_23 = lean_array_push(x_22, x_21);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_14);
lean_ctor_set(x_24, 2, x_15);
lean_ctor_set(x_24, 3, x_16);
return x_24;
}
}
}
lean_object* l_Lean_Parser_ParserState_mkTrailingNode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_mkTrailingNode(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_ParserState_mkError_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_ParserState_mkError_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_ParserState_mkError_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_ParserState_mkError(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 3);
lean_dec(x_4);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_instInhabitedParserDescr___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_1, 3, x_9);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_instInhabitedParserDescr___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_12);
lean_ctor_set(x_18, 3, x_17);
return x_18;
}
}
}
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_ParserState_mkUnexpectedError_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 3);
lean_dec(x_4);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_1, 3, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_13);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkEOIError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("end of input");
return x_1;
}
}
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_3 = l_Lean_Parser_ParserState_mkUnexpectedError(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_ParserState_mkErrorAt_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_ParserState_mkErrorAt_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_ParserState_mkErrorAt_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 3);
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_dec(x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_instInhabitedParserDescr___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_1, 3, x_11);
lean_ctor_set(x_1, 1, x_3);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_instInhabitedParserDescr___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_19, 2, x_13);
lean_ctor_set(x_19, 3, x_18);
return x_19;
}
}
}
lean_object* l_Lean_Parser_ParserState_mkErrorsAt_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_ParserState_mkErrorsAt_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_ParserState_mkErrorsAt_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 3);
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_dec(x_6);
x_7 = l_Lean_instInhabitedParserDescr___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_1, 3, x_9);
lean_ctor_set(x_1, 1, x_3);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_Lean_instInhabitedParserDescr___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_14);
return x_15;
}
}
}
lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_ParserState_mkUnexpectedErrorAt_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 3);
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_dec(x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_1, 3, x_9);
lean_ctor_set(x_1, 1, x_3);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_14);
return x_15;
}
}
}
lean_object* l_Lean_Parser_instInhabitedParserFn___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_instInhabitedParserFn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_instInhabitedParserFn___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_instInhabitedParserFn___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instInhabitedParserFn___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_instInhabitedParserFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instInhabitedParserFn(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Lean_Parser_FirstTokens_seq_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_apply_1(x_3, x_2);
return x_7;
}
case 3:
{
lean_dec(x_3);
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_apply_2(x_5, x_8, x_9);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_apply_2(x_4, x_11, x_12);
return x_13;
}
default: 
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
x_14 = lean_apply_2(x_6, x_1, x_2);
return x_14;
}
}
}
default: 
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_apply_2(x_6, x_1, x_2);
return x_15;
}
}
}
}
lean_object* l_Lean_Parser_FirstTokens_seq_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_FirstTokens_seq_match__1___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_FirstTokens_seq(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
return x_2;
}
case 3:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_List_append___rarg(x_3, x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_List_append___rarg(x_3, x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
case 3:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = l_List_append___rarg(x_10, x_12);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_List_append___rarg(x_10, x_14);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
default: 
{
lean_dec(x_2);
return x_1;
}
}
}
default: 
{
lean_dec(x_2);
return x_1;
}
}
}
}
lean_object* l_Lean_Parser_FirstTokens_toOptional_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l_Lean_Parser_FirstTokens_toOptional_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_FirstTokens_toOptional_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_ctor_set_tag(x_1, 3);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
return x_1;
}
}
}
lean_object* l_Lean_Parser_FirstTokens_merge_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_apply_1(x_3, x_2);
return x_10;
}
case 1:
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_11; 
lean_dec(x_9);
x_11 = lean_apply_1(x_4, x_1);
return x_11;
}
case 1:
{
lean_object* x_12; 
lean_dec(x_4);
x_12 = lean_apply_2(x_9, x_2, x_2);
return x_12;
}
default: 
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_apply_2(x_9, x_1, x_2);
return x_13;
}
}
}
case 2:
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
x_14 = lean_apply_1(x_4, x_1);
return x_14;
}
case 1:
{
lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_apply_2(x_9, x_1, x_2);
return x_15;
}
case 2:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_apply_2(x_5, x_16, x_17);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_apply_2(x_7, x_19, x_20);
return x_21;
}
}
}
default: 
{
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_22 = lean_apply_1(x_4, x_1);
return x_22;
}
case 1:
{
lean_object* x_23; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_23 = lean_apply_2(x_9, x_1, x_2);
return x_23;
}
case 2:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
lean_dec(x_2);
x_26 = lean_apply_2(x_8, x_24, x_25);
return x_26;
}
default: 
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_apply_2(x_6, x_27, x_28);
return x_29;
}
}
}
}
}
}
lean_object* l_Lean_Parser_FirstTokens_merge_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_FirstTokens_merge_match__1___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_FirstTokens_merge(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_FirstTokens_toOptional(x_2);
return x_3;
}
case 1:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Parser_FirstTokens_toOptional(x_1);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(1);
return x_5;
}
}
case 2:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_FirstTokens_toOptional(x_1);
return x_6;
}
case 1:
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_box(1);
return x_7;
}
case 2:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = l_List_append___rarg(x_8, x_10);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_List_append___rarg(x_8, x_12);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
default: 
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = l_List_append___rarg(x_15, x_17);
lean_ctor_set(x_2, 0, x_18);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l_List_append___rarg(x_15, x_19);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_22; 
x_22 = l_Lean_Parser_FirstTokens_toOptional(x_1);
return x_22;
}
case 1:
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = lean_box(1);
return x_23;
}
case 2:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = l_List_append___rarg(x_24, x_26);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec(x_2);
x_29 = l_List_append___rarg(x_24, x_28);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
default: 
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_2);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = l_List_append___rarg(x_31, x_33);
lean_ctor_set(x_2, 0, x_34);
return x_2;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_2, 0);
lean_inc(x_35);
lean_dec(x_2);
x_36 = l_List_append___rarg(x_31, x_35);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
}
}
}
lean_object* l_Lean_Parser_FirstTokens_toStr_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_1(x_5, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Parser_FirstTokens_toStr_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_FirstTokens_toStr_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_List_toStringAux___at_Lean_Parser_FirstTokens_toStr___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Lean_instInhabitedParserDescr___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_term_x5b___x5d___closed__5;
x_7 = lean_string_append(x_6, x_4);
lean_dec(x_4);
x_8 = 0;
x_9 = l_List_toStringAux___at_Lean_Parser_FirstTokens_toStr___spec__2(x_8, x_5);
x_10 = lean_string_append(x_7, x_9);
lean_dec(x_9);
return x_10;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; 
x_11 = l_Lean_instInhabitedParserDescr___closed__1;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = 0;
x_15 = l_List_toStringAux___at_Lean_Parser_FirstTokens_toStr___spec__2(x_14, x_13);
x_16 = lean_string_append(x_12, x_15);
lean_dec(x_15);
return x_16;
}
}
}
}
lean_object* l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_instReprList___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = 1;
x_5 = l_List_toStringAux___at_Lean_Parser_FirstTokens_toStr___spec__2(x_4, x_1);
x_6 = l_term_x5b___x5d___closed__3;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_term_x5b___x5d___closed__9;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 1;
x_14 = l_List_toStringAux___at_Lean_Parser_FirstTokens_toStr___spec__2(x_13, x_12);
x_15 = l_term_x5b___x5d___closed__3;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_term_x5b___x5d___closed__9;
x_18 = lean_string_append(x_16, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Parser_FirstTokens_toStr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("epsilon");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_FirstTokens_toStr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown");
return x_1;
}
}
lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_FirstTokens_toStr___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_FirstTokens_toStr___closed__2;
return x_3;
}
case 2:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1(x_4);
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1(x_6);
x_8 = l_stx___x3f___closed__3;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
return x_9;
}
}
}
}
lean_object* l_List_toStringAux___at_Lean_Parser_FirstTokens_toStr___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___at_Lean_Parser_FirstTokens_toStr___spec__2(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_FirstTokens_instToStringFirstTokens___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_FirstTokens_toStr), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_FirstTokens_instToStringFirstTokens() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_FirstTokens_instToStringFirstTokens___closed__1;
return x_1;
}
}
lean_object* l_Lean_Parser_ParserInfo_collectTokens___default(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_ParserInfo_collectTokens___default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ParserInfo_collectTokens___default(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_ParserInfo_collectKinds___default(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_ParserInfo_collectKinds___default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ParserInfo_collectKinds___default(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_ParserInfo_firstTokens___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(1);
return x_1;
}
}
lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_instInhabitedParserInfo___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserInfo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_instInhabitedParserInfo___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_instInhabitedParserInfo___closed__1;
x_2 = l_Lean_Parser_instInhabitedParserInfo___closed__2;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instInhabitedParserInfo___closed__3;
return x_1;
}
}
lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instInhabitedParserInfo___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instInhabitedParserInfo___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_Parser_info___default___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_Parser_info___default___elambda__2(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Parser_info___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Parser_info___default___elambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Parser_info___default___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Parser_info___default___elambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Parser_info___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Parser_info___default___closed__1;
x_2 = l_Lean_Parser_Parser_info___default___closed__2;
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Parser_info___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Parser_info___default___closed__3;
return x_1;
}
}
lean_object* l_Lean_Parser_Parser_info___default___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Parser_info___default___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_Parser_info___default___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Parser_info___default___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_instInhabitedParser___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_instInhabitedParser___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParser___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_instInhabitedParserInfo___closed__3;
x_2 = l_Lean_Parser_instInhabitedParser___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParser() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instInhabitedParser___closed__2;
return x_1;
}
}
lean_object* l_Lean_Parser_instInhabitedParser___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_instInhabitedParser___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_epsilonInfo___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_epsilonInfo___elambda__2(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_epsilonInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___elambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_epsilonInfo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_epsilonInfo___elambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_epsilonInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_epsilonInfo___closed__1;
x_2 = l_Lean_Parser_epsilonInfo___closed__2;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_epsilonInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_epsilonInfo___closed__3;
return x_1;
}
}
lean_object* l_Lean_Parser_epsilonInfo___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_epsilonInfo___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_epsilonInfo___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_epsilonInfo___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_checkStackTopFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_5);
lean_dec(x_5);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_2);
return x_9;
}
else
{
lean_dec(x_2);
return x_4;
}
}
}
lean_object* l_Lean_Parser_checkStackTopFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_checkStackTopFn(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_checkStackTop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_checkStackTopFn___boxed), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = l_Lean_Parser_epsilonInfo;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_andthenFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_9; 
x_9 = lean_apply_2(x_2, x_3, x_5);
return x_9;
}
}
}
lean_object* l_Lean_Parser_andthenInfo___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_andthenInfo___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_andthenInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___elambda__2), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___elambda__1), 3, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Parser_FirstTokens_seq(x_9, x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
lean_object* l_Lean_Parser_andthen(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_andthenInfo(x_3, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Parser_instAndThenParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_andthen), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instAndThenParser() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instAndThenParser___closed__1;
return x_1;
}
}
lean_object* l_Lean_Parser_nodeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_7 = lean_apply_2(x_2, x_3, x_4);
x_8 = l_Lean_Parser_ParserState_mkNode(x_7, x_1, x_6);
return x_8;
}
}
lean_object* l_Lean_Parser_trailingNodeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_7 = lean_apply_2(x_2, x_3, x_4);
x_8 = l_Lean_Parser_ParserState_mkTrailingNode(x_7, x_1, x_6);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Lean_Parser_nodeInfo___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_3);
x_6 = lean_box(0);
x_7 = l_Std_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(x_5, x_1, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_nodeInfo___elambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_nodeInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_nodeInfo___elambda__2), 2, 1);
lean_closure_set(x_3, 0, x_2);
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_nodeInfo___elambda__1), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 1);
lean_dec(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_dec(x_7);
lean_ctor_set(x_2, 1, x_4);
lean_ctor_set(x_2, 0, x_3);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Parser_node(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_1);
x_4 = l_Lean_Parser_nodeInfo(x_1, x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_errorFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_errorFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_errorFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_error(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_errorFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_epsilonInfo;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_errorAtSavedPosFn_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_errorAtSavedPosFn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_errorAtSavedPosFn_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_errorAtSavedPosFn_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_errorAtSavedPosFn_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_errorAtSavedPosFn_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_errorAtSavedPosFn(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 4);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
else
{
if (x_2 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_4, 3);
lean_dec(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_dec(x_10);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_5, 0, x_12);
lean_ctor_set(x_4, 3, x_5);
lean_ctor_set(x_4, 1, x_8);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_5, 0, x_17);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_5);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 2);
lean_inc(x_21);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_22 = x_4;
} else {
 lean_dec_ref(x_4);
 x_22 = lean_box(0);
}
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
if (lean_is_scalar(x_22)) {
 x_26 = lean_alloc_ctor(0, 4, 0);
} else {
 x_26 = x_22;
}
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_19);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_5);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
lean_dec(x_3);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_string_utf8_next(x_30, x_28);
lean_dec(x_28);
lean_dec(x_30);
x_32 = !lean_is_exclusive(x_4);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_4, 3);
lean_dec(x_33);
x_34 = lean_ctor_get(x_4, 1);
lean_dec(x_34);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_5, 0, x_36);
lean_ctor_set(x_4, 3, x_5);
lean_ctor_set(x_4, 1, x_31);
return x_4;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_4, 0);
x_38 = lean_ctor_get(x_4, 2);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_4);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_5, 0, x_40);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_31);
lean_ctor_set(x_41, 2, x_38);
lean_ctor_set(x_41, 3, x_5);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_42 = lean_ctor_get(x_5, 0);
lean_inc(x_42);
lean_dec(x_5);
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_string_utf8_next(x_44, x_42);
lean_dec(x_42);
lean_dec(x_44);
x_46 = lean_ctor_get(x_4, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_4, 2);
lean_inc(x_47);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_48 = x_4;
} else {
 lean_dec_ref(x_4);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
if (lean_is_scalar(x_48)) {
 x_52 = lean_alloc_ctor(0, 4, 0);
} else {
 x_52 = x_48;
}
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_45);
lean_ctor_set(x_52, 2, x_47);
lean_ctor_set(x_52, 3, x_51);
return x_52;
}
}
}
}
}
lean_object* l_Lean_Parser_errorAtSavedPosFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Parser_errorAtSavedPosFn(x_1, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_errorAtSavedPos___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Applicative_seqRight___default___rarg___closed__1;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_errorAtSavedPos(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_errorAtSavedPosFn___boxed), 4, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = l_Lean_Parser_errorAtSavedPos___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Parser_errorAtSavedPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Parser_errorAtSavedPos(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_checkPrecFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected token at this precedence level; consider parenthesizing the term");
return x_1;
}
}
lean_object* l_Lean_Parser_checkPrecFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_nat_dec_le(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Parser_checkPrecFn___closed__1;
x_7 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_6);
return x_7;
}
else
{
return x_3;
}
}
}
lean_object* l_Lean_Parser_checkPrecFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkPrecFn(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_checkPrec(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_epsilonInfo;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_checkInsideQuotFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected syntax outside syntax quotation");
return x_1;
}
}
lean_object* l_Lean_Parser_checkInsideQuotFn(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parser_checkInsideQuotFn___closed__1;
x_5 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_4);
return x_5;
}
else
{
return x_2;
}
}
}
lean_object* l_Lean_Parser_checkInsideQuotFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_checkInsideQuotFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_checkInsideQuot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_checkInsideQuotFn___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_checkInsideQuot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_checkInsideQuot___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_checkInsideQuot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_checkInsideQuot___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_checkOutsideQuotFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected syntax inside syntax quotation");
return x_1;
}
}
lean_object* l_Lean_Parser_checkOutsideQuotFn(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parser_checkOutsideQuotFn___closed__1;
x_5 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_4);
return x_5;
}
}
}
lean_object* l_Lean_Parser_checkOutsideQuotFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_checkOutsideQuotFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_checkOutsideQuot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_checkOutsideQuotFn___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_checkOutsideQuot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_checkOutsideQuot___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_checkOutsideQuot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_checkOutsideQuot___closed__2;
return x_1;
}
}
lean_object* l_Lean_Parser_toggleInsideQuotFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
lean_ctor_set_uint8(x_2, sizeof(void*)*6, x_11);
x_12 = lean_apply_2(x_1, x_2, x_3);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
lean_ctor_set_uint8(x_2, sizeof(void*)*6, x_13);
x_14 = lean_apply_2(x_1, x_2, x_3);
return x_14;
}
}
else
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
x_18 = lean_ctor_get(x_8, 2);
x_19 = lean_ctor_get(x_8, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_19);
if (x_15 == 0)
{
uint8_t x_21; lean_object* x_22; 
x_21 = 1;
lean_ctor_set(x_2, 1, x_20);
lean_ctor_set_uint8(x_2, sizeof(void*)*6, x_21);
x_22 = lean_apply_2(x_1, x_2, x_3);
return x_22;
}
else
{
uint8_t x_23; lean_object* x_24; 
x_23 = 0;
lean_ctor_set(x_2, 1, x_20);
lean_ctor_set_uint8(x_2, sizeof(void*)*6, x_23);
x_24 = lean_apply_2(x_1, x_2, x_3);
return x_24;
}
}
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_27 = lean_ctor_get(x_6, 0);
x_28 = lean_ctor_get(x_6, 1);
x_29 = lean_ctor_get(x_6, 2);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_6);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_25, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_25, 3);
lean_inc(x_34);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 x_35 = x_25;
} else {
 lean_dec_ref(x_25);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 4, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_34);
if (x_26 == 0)
{
uint8_t x_37; lean_object* x_38; 
x_37 = 1;
lean_ctor_set(x_2, 1, x_36);
lean_ctor_set(x_2, 0, x_30);
lean_ctor_set_uint8(x_2, sizeof(void*)*6, x_37);
x_38 = lean_apply_2(x_1, x_2, x_3);
return x_38;
}
else
{
uint8_t x_39; lean_object* x_40; 
x_39 = 0;
lean_ctor_set(x_2, 1, x_36);
lean_ctor_set(x_2, 0, x_30);
lean_ctor_set_uint8(x_2, sizeof(void*)*6, x_39);
x_40 = lean_apply_2(x_1, x_2, x_3);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_41 = lean_ctor_get(x_2, 0);
x_42 = lean_ctor_get(x_2, 1);
x_43 = lean_ctor_get(x_2, 2);
x_44 = lean_ctor_get(x_2, 3);
x_45 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_46 = lean_ctor_get(x_2, 4);
x_47 = lean_ctor_get(x_2, 5);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_2);
x_48 = lean_ctor_get(x_41, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_41, 2);
lean_inc(x_50);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 x_51 = x_41;
} else {
 lean_dec_ref(x_41);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 3, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 2, x_50);
x_53 = lean_ctor_get(x_42, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_42, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_42, 3);
lean_inc(x_56);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_57 = x_42;
} else {
 lean_dec_ref(x_42);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 4, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_54);
lean_ctor_set(x_58, 2, x_55);
lean_ctor_set(x_58, 3, x_56);
if (x_45 == 0)
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_59 = 1;
x_60 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_43);
lean_ctor_set(x_60, 3, x_44);
lean_ctor_set(x_60, 4, x_46);
lean_ctor_set(x_60, 5, x_47);
lean_ctor_set_uint8(x_60, sizeof(void*)*6, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*6 + 1, x_4);
x_61 = lean_apply_2(x_1, x_60, x_3);
return x_61;
}
else
{
uint8_t x_62; lean_object* x_63; lean_object* x_64; 
x_62 = 0;
x_63 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_63, 0, x_52);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_43);
lean_ctor_set(x_63, 3, x_44);
lean_ctor_set(x_63, 4, x_46);
lean_ctor_set(x_63, 5, x_47);
lean_ctor_set_uint8(x_63, sizeof(void*)*6, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*6 + 1, x_4);
x_64 = lean_apply_2(x_1, x_63, x_3);
return x_64;
}
}
}
else
{
lean_object* x_65; 
x_65 = lean_apply_2(x_1, x_2, x_3);
return x_65;
}
}
}
lean_object* l_Lean_Parser_toggleInsideQuot(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_toggleInsideQuotFn), 3, 1);
lean_closure_set(x_4, 0, x_3);
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_toggleInsideQuotFn), 3, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Parser_suppressInsideQuotFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 1, x_9);
x_10 = lean_apply_2(x_1, x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_ctor_get(x_7, 2);
x_14 = lean_ctor_get(x_7, 3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set(x_15, 3, x_14);
x_16 = 1;
lean_ctor_set(x_2, 1, x_15);
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 1, x_16);
x_17 = lean_apply_2(x_1, x_2, x_3);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
x_21 = lean_ctor_get(x_5, 2);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_18, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_18, 3);
lean_inc(x_26);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 x_27 = x_18;
} else {
 lean_dec_ref(x_18);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 4, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
x_29 = 1;
lean_ctor_set(x_2, 1, x_28);
lean_ctor_set(x_2, 0, x_22);
lean_ctor_set_uint8(x_2, sizeof(void*)*6 + 1, x_29);
x_30 = lean_apply_2(x_1, x_2, x_3);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_31 = lean_ctor_get(x_2, 0);
x_32 = lean_ctor_get(x_2, 1);
x_33 = lean_ctor_get(x_2, 2);
x_34 = lean_ctor_get(x_2, 3);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_36 = lean_ctor_get(x_2, 4);
x_37 = lean_ctor_get(x_2, 5);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_2);
x_38 = lean_ctor_get(x_31, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_31, 2);
lean_inc(x_40);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_41 = x_31;
} else {
 lean_dec_ref(x_31);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 3, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_40);
x_43 = lean_ctor_get(x_32, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_32, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_32, 3);
lean_inc(x_46);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 x_47 = x_32;
} else {
 lean_dec_ref(x_32);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 4, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_45);
lean_ctor_set(x_48, 3, x_46);
x_49 = 1;
x_50 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set(x_50, 2, x_33);
lean_ctor_set(x_50, 3, x_34);
lean_ctor_set(x_50, 4, x_36);
lean_ctor_set(x_50, 5, x_37);
lean_ctor_set_uint8(x_50, sizeof(void*)*6, x_35);
lean_ctor_set_uint8(x_50, sizeof(void*)*6 + 1, x_49);
x_51 = lean_apply_2(x_1, x_50, x_3);
return x_51;
}
}
}
lean_object* l_Lean_Parser_suppressInsideQuot(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_suppressInsideQuotFn), 3, 1);
lean_closure_set(x_4, 0, x_3);
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_suppressInsideQuotFn), 3, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Parser_leadingNode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_inc(x_1);
x_6 = l_Lean_Parser_nodeInfo(x_1, x_5);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_epsilonInfo;
x_10 = l_Lean_Parser_andthenInfo(x_9, x_6);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
lean_object* l_Lean_Parser_trailingNodeAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_1);
x_4 = l_Lean_Parser_nodeInfo(x_1, x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_trailingNodeFn), 4, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_trailingNode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_inc(x_1);
x_6 = l_Lean_Parser_nodeInfo(x_1, x_5);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_trailingNodeFn), 4, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_epsilonInfo;
x_10 = l_Lean_Parser_andthenInfo(x_9, x_6);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
lean_object* l_Lean_Parser_mergeOrElseErrors_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_apply_1(x_3, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_apply_4(x_2, x_6, x_7, x_8, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Parser_mergeOrElseErrors_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_mergeOrElseErrors_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_nat_dec_eq(x_7, x_3);
if (x_11 == 0)
{
lean_free_object(x_5);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 0);
lean_dec(x_16);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Parser_Error_merge(x_2, x_10);
lean_ctor_set(x_5, 0, x_17);
return x_1;
}
}
else
{
lean_dec(x_1);
if (x_4 == 0)
{
lean_object* x_18; 
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_7);
lean_ctor_set(x_18, 2, x_8);
lean_ctor_set(x_18, 3, x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_Parser_Error_merge(x_2, x_10);
lean_ctor_set(x_5, 0, x_19);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_7);
lean_ctor_set(x_20, 2, x_8);
lean_ctor_set(x_20, 3, x_5);
return x_20;
}
}
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_5, 0);
lean_inc(x_21);
lean_dec(x_5);
x_22 = lean_nat_dec_eq(x_7, x_3);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_23; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_23 = x_1;
} else {
 lean_dec_ref(x_1);
 x_23 = lean_box(0);
}
if (x_4 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_21);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 4, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_7);
lean_ctor_set(x_25, 2, x_8);
lean_ctor_set(x_25, 3, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = l_Lean_Parser_Error_merge(x_2, x_21);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
if (lean_is_scalar(x_23)) {
 x_28 = lean_alloc_ctor(0, 4, 0);
} else {
 x_28 = x_23;
}
lean_ctor_set(x_28, 0, x_6);
lean_ctor_set(x_28, 1, x_7);
lean_ctor_set(x_28, 2, x_8);
lean_ctor_set(x_28, 3, x_27);
return x_28;
}
}
}
}
}
}
lean_object* l_Lean_Parser_mergeOrElseErrors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_mergeOrElseErrors(x_1, x_2, x_3, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Parser_orelseFnCore_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_orelseFnCore_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_orelseFnCore_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_orelseFnCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_4);
x_9 = lean_apply_2(x_1, x_4, x_5);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_12, x_8);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_8);
x_14 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean_dec(x_7);
x_15 = lean_apply_2(x_2, x_4, x_14);
x_16 = l_Lean_Parser_mergeOrElseErrors(x_15, x_11, x_8, x_3);
lean_dec(x_8);
return x_16;
}
}
}
}
lean_object* l_Lean_Parser_orelseFnCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Parser_orelseFnCore(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_orelseFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
x_6 = l_Lean_Parser_orelseFnCore(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Parser_orelseInfo___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_orelseInfo___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_orelseInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_orelseInfo___elambda__2), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_orelseInfo___elambda__1), 3, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Parser_FirstTokens_merge(x_9, x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
lean_object* l_Lean_Parser_orelse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_orelseInfo(x_3, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn), 4, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Parser_instOrElseParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_orelse), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instOrElseParser() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instOrElseParser___closed__1;
return x_1;
}
}
lean_object* l_Lean_Parser_noFirstTokenInfo___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_noFirstTokenInfo___elambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_noFirstTokenInfo___elambda__2), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_noFirstTokenInfo___elambda__1), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_atomicFn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_apply_1(x_3, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_apply_4(x_2, x_6, x_7, x_8, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Parser_atomicFn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_atomicFn_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_atomicFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_array_get_size(x_4);
lean_dec(x_4);
x_7 = lean_apply_2(x_1, x_2, x_3);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 3);
lean_dec(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Array_shrink___rarg(x_10, x_6);
lean_dec(x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = l_Array_shrink___rarg(x_10, x_6);
lean_dec(x_6);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_7, 3, x_17);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 2);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_21 = x_8;
} else {
 lean_dec_ref(x_8);
 x_21 = lean_box(0);
}
x_22 = l_Array_shrink___rarg(x_18, x_6);
lean_dec(x_6);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(1, 1, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_20);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Parser_atomic(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_atomicFn), 3, 1);
lean_closure_set(x_4, 0, x_3);
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_atomicFn), 3, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Parser_optionalFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_apply_2(x_1, x_2, x_3);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
x_12 = lean_nat_dec_eq(x_11, x_6);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_13 = l_Lean_nullKind;
x_14 = l_Lean_Parser_ParserState_mkNode(x_7, x_13, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Parser_ParserState_restore(x_7, x_5, x_6);
x_16 = l_Lean_nullKind;
x_17 = l_Lean_Parser_ParserState_mkNode(x_15, x_16, x_5);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
x_18 = l_Lean_nullKind;
x_19 = l_Lean_Parser_ParserState_mkNode(x_7, x_18, x_5);
return x_19;
}
}
}
lean_object* l_Lean_Parser_optionaInfo___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_optionaInfo___elambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_optionaInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_optionaInfo___elambda__2), 2, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_optionaInfo___elambda__1), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Parser_FirstTokens_toOptional(x_4);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_optionaInfo(x_2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_optionalFn), 3, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_lookaheadFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_apply_2(x_1, x_2, x_3);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_11; 
x_11 = l_Lean_Parser_ParserState_restore(x_7, x_5, x_6);
lean_dec(x_5);
return x_11;
}
}
}
lean_object* l_Lean_Parser_lookahead(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn), 3, 1);
lean_closure_set(x_4, 0, x_3);
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn), 3, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
static lean_object* _init_l_Lean_Parser_notFollowedByFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected ");
return x_1;
}
}
lean_object* l_Lean_Parser_notFollowedByFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_apply_2(x_1, x_3, x_4);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
lean_dec(x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
lean_dec(x_6);
x_14 = l_Lean_Parser_notFollowedByFn___closed__1;
x_15 = lean_string_append(x_14, x_2);
x_16 = l_Lean_instInhabitedParserDescr___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Lean_Parser_ParserState_mkUnexpectedError(x_13, x_17);
return x_18;
}
}
}
lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_notFollowedByFn(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Parser_notFollowedBy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByFn___boxed), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Lean_Parser_errorAtSavedPos___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_manyAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'many' parser combinator application, parser did not consume anything");
return x_1;
}
}
lean_object* l_Lean_Parser_manyAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_2);
x_7 = lean_apply_2(x_1, x_2, x_3);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
x_12 = lean_nat_dec_eq(x_6, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Parser_ParserState_restore(x_7, x_5, x_6);
lean_dec(x_5);
return x_13;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_5);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
x_15 = lean_nat_dec_eq(x_6, x_14);
lean_dec(x_14);
lean_dec(x_6);
if (x_15 == 0)
{
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Parser_manyAux___closed__1;
x_18 = l_Lean_Parser_ParserState_mkUnexpectedError(x_7, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Parser_manyFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_manyAux(x_1, x_2, x_3);
x_7 = l_Lean_nullKind;
x_8 = l_Lean_Parser_ParserState_mkNode(x_6, x_7, x_5);
return x_8;
}
}
lean_object* l_Lean_Parser_manyNoAntiquot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_noFirstTokenInfo(x_2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_manyFn), 3, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_many1Fn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_2);
x_6 = lean_apply_2(x_1, x_2, x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lean_nullKind;
x_11 = l_Lean_Parser_ParserState_mkNode(x_6, x_10, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Parser_manyAux(x_1, x_2, x_6);
x_13 = l_Lean_nullKind;
x_14 = l_Lean_Parser_ParserState_mkNode(x_12, x_13, x_5);
return x_14;
}
}
}
lean_object* l_Lean_Parser_many1NoAntiquot(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn), 3, 1);
lean_closure_set(x_4, 0, x_3);
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn), 3, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_6);
x_11 = lean_apply_2(x_1, x_6, x_7);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
x_16 = lean_nat_dec_lt(x_10, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
if (x_5 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
x_17 = lean_box(0);
x_18 = l_Lean_Parser_ParserState_pushSyntax(x_11, x_17);
x_19 = l_Lean_nullKind;
x_20 = l_Lean_Parser_ParserState_mkNode(x_18, x_19, x_4);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_Parser_ParserState_restore(x_11, x_9, x_10);
lean_dec(x_9);
x_22 = l_Lean_nullKind;
x_23 = l_Lean_Parser_ParserState_mkNode(x_21, x_22, x_4);
return x_23;
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
return x_11;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
x_25 = lean_array_get_size(x_24);
lean_dec(x_24);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_2);
lean_inc(x_6);
x_27 = lean_apply_2(x_2, x_6, x_11);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
x_29 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_28, x_13);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_30 = l_Lean_Parser_ParserState_restore(x_27, x_25, x_26);
lean_dec(x_25);
x_31 = l_Lean_nullKind;
x_32 = l_Lean_Parser_ParserState_mkNode(x_30, x_31, x_4);
return x_32;
}
else
{
lean_dec(x_26);
lean_dec(x_25);
{
uint8_t _tmp_4 = x_3;
lean_object* _tmp_6 = x_27;
x_5 = _tmp_4;
x_7 = _tmp_6;
}
goto _start;
}
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(x_1, x_2, x_8, x_4, x_9, x_6, x_7);
return x_10;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(x_1, x_2, x_8, x_4, x_9, x_6, x_7);
return x_10;
}
}
lean_object* l_Lean_Parser_sepByFn(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(x_2, x_3, x_1, x_7, x_8, x_4, x_5);
return x_9;
}
}
lean_object* l_Lean_Parser_sepByFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Parser_sepByFn(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_sepBy1Fn(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(x_2, x_3, x_1, x_7, x_8, x_4, x_5);
return x_9;
}
}
lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Parser_sepBy1Fn(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_sepByInfo___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_sepByInfo___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_sepByInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_sepByInfo___elambda__2), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_sepByInfo___elambda__1), 3, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
}
lean_object* l_Lean_Parser_sepBy1Info___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_sepBy1Info___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_sepBy1Info(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Info___elambda__2), 3, 2);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Info___elambda__1), 3, 2);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_8);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Info___elambda__2), 3, 2);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Info___elambda__1), 3, 2);
lean_closure_set(x_16, 0, x_11);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_12);
return x_17;
}
}
}
lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = l_Lean_Parser_sepByInfo(x_4, x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_sepByFn___boxed), 5, 3);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
lean_object* l_Lean_Parser_sepByNoAntiquot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Parser_sepByNoAntiquot(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = l_Lean_Parser_sepBy1Info(x_4, x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Fn___boxed), 5, 3);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
lean_object* l_Lean_Parser_sepBy1NoAntiquot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Parser_sepBy1NoAntiquot(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_withResultOfFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_9);
lean_dec(x_9);
x_11 = l_Lean_Parser_ParserState_popSyntax(x_5);
x_12 = lean_apply_1(x_2, x_10);
x_13 = l_Lean_Parser_ParserState_pushSyntax(x_11, x_12);
return x_13;
}
}
}
lean_object* l_Lean_Parser_withResultOfInfo___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_withResultOfInfo___elambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_withResultOfInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_withResultOfInfo___elambda__2), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_withResultOfInfo___elambda__1), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_withResultOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l_Lean_Parser_withResultOfInfo(x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_withResultOfFn), 4, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_many1Unbox___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Syntax_getNumArgs(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
return x_6;
}
}
}
static lean_object* _init_l_Lean_Parser_many1Unbox___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_many1Unbox___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_many1Unbox(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn), 3, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_Parser_withResultOfInfo(x_2);
x_6 = l_Lean_Parser_many1Unbox___closed__1;
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_withResultOfFn), 4, 2);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
lean_object* l_Lean_Parser_many1Unbox___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_many1Unbox___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_satisfyFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_string_utf8_at_end(x_7, x_5);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get(x_7, x_5);
x_10 = lean_box_uint32(x_9);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_5);
x_13 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_2);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = l_Lean_Parser_ParserState_next(x_4, x_7, x_5);
lean_dec(x_5);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_16 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_15);
return x_16;
}
}
}
lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_satisfyFn(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_takeUntilFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_string_utf8_at_end(x_6, x_4);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_string_utf8_get(x_6, x_4);
x_9 = lean_box_uint32(x_8);
lean_inc(x_1);
x_10 = lean_apply_1(x_1, x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Parser_ParserState_next(x_3, x_6, x_4);
lean_dec(x_4);
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l_Lean_Parser_takeUntilFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_takeUntilFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_takeWhileFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_String_all___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Parser_takeUntilFn(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_takeWhileFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_takeWhileFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_takeWhile1Fn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_1);
x_5 = l_Lean_Parser_satisfyFn(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_9; 
x_9 = l_Lean_Parser_takeWhileFn(x_1, x_3, x_5);
return x_9;
}
}
}
lean_object* l_Lean_Parser_takeWhile1Fn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_takeWhile1Fn(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_finishCommentBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_string_utf8_at_end(x_5, x_6);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; uint32_t x_10; uint8_t x_11; 
x_8 = lean_string_utf8_get(x_5, x_6);
x_9 = lean_string_utf8_next(x_5, x_6);
lean_dec(x_6);
x_10 = 45;
x_11 = x_8 == x_10;
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 47;
x_13 = x_8 == x_12;
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Parser_ParserState_setPos(x_3, x_9);
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = lean_string_utf8_at_end(x_5, x_9);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = lean_string_utf8_get(x_5, x_9);
x_18 = x_17 == x_10;
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_Parser_ParserState_setPos(x_3, x_9);
x_3 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_1, x_21);
lean_dec(x_1);
x_23 = l_Lean_Parser_ParserState_next(x_3, x_5, x_9);
lean_dec(x_9);
x_1 = x_22;
x_3 = x_23;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
lean_dec(x_1);
x_25 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_26 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = lean_string_utf8_at_end(x_5, x_9);
if (x_27 == 0)
{
uint32_t x_28; uint32_t x_29; uint8_t x_30; 
x_28 = lean_string_utf8_get(x_5, x_9);
x_29 = 47;
x_30 = x_28 == x_29;
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_Parser_ParserState_next(x_3, x_5, x_9);
lean_dec(x_9);
x_3 = x_31;
goto _start;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_dec_eq(x_1, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_nat_sub(x_1, x_33);
lean_dec(x_1);
x_36 = l_Lean_Parser_ParserState_next(x_3, x_5, x_9);
lean_dec(x_9);
x_1 = x_35;
x_3 = x_36;
goto _start;
}
else
{
lean_object* x_38; 
lean_dec(x_1);
x_38 = l_Lean_Parser_ParserState_next(x_3, x_5, x_9);
lean_dec(x_9);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_9);
lean_dec(x_1);
x_39 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_40 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_6);
lean_dec(x_1);
x_41 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_42 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_41);
return x_42;
}
}
}
lean_object* l_Lean_Parser_finishCommentBlock___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_finishCommentBlock(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
uint8_t l_Lean_Parser_whitespace___lambda__1(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 10;
x_3 = x_1 == x_2;
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_whitespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_whitespace___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_whitespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_at_end(x_4, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = lean_string_utf8_get(x_4, x_5);
x_8 = l_Char_isWhitespace(x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 45;
x_10 = x_7 == x_9;
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 47;
x_12 = x_7 == x_11;
if (x_12 == 0)
{
lean_dec(x_5);
return x_2;
}
else
{
lean_object* x_13; uint32_t x_14; uint8_t x_15; 
x_13 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
x_14 = lean_string_utf8_get(x_4, x_13);
x_15 = x_14 == x_9;
if (x_15 == 0)
{
lean_dec(x_13);
return x_2;
}
else
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_16 = lean_string_utf8_next(x_4, x_13);
lean_dec(x_13);
x_17 = lean_string_utf8_get(x_4, x_16);
x_18 = x_17 == x_9;
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = l_Lean_Parser_ParserState_next(x_2, x_4, x_16);
lean_dec(x_16);
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_Parser_finishCommentBlock(x_20, x_1, x_19);
x_22 = lean_ctor_get(x_21, 3);
lean_inc(x_22);
x_23 = lean_box(0);
x_24 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
return x_21;
}
else
{
x_2 = x_21;
goto _start;
}
}
else
{
lean_dec(x_16);
return x_2;
}
}
}
}
else
{
lean_object* x_26; uint32_t x_27; uint8_t x_28; 
x_26 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
x_27 = lean_string_utf8_get(x_4, x_26);
x_28 = x_27 == x_9;
if (x_28 == 0)
{
lean_dec(x_26);
return x_2;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = l_Lean_Parser_ParserState_next(x_2, x_4, x_26);
lean_dec(x_26);
x_30 = l_Lean_Parser_whitespace___closed__1;
x_31 = l_Lean_Parser_takeUntilFn(x_30, x_1, x_29);
x_32 = lean_ctor_get(x_31, 3);
lean_inc(x_32);
x_33 = lean_box(0);
x_34 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
return x_31;
}
else
{
x_2 = x_31;
goto _start;
}
}
}
}
else
{
lean_object* x_36; 
x_36 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_5);
x_2 = x_36;
goto _start;
}
}
else
{
lean_dec(x_5);
return x_2;
}
}
}
lean_object* l_Lean_Parser_whitespace___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_whitespace___lambda__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_whitespace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_whitespace(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_mkEmptySubstringAt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc_n(x_1, 2);
lean_inc(x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 2, x_1);
x_9 = lean_string_utf8_extract(x_6, x_1, x_7);
if (x_2 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_7);
lean_inc(x_6);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_7);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
x_16 = l_Lean_Parser_ParserState_pushSyntax(x_4, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = l_Lean_Parser_whitespace(x_3, x_4);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_inc(x_6);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_7);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_8);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_9);
x_25 = l_Lean_Parser_ParserState_pushSyntax(x_17, x_24);
return x_25;
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Parser_rawFn(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_inc(x_3);
x_6 = lean_apply_2(x_1, x_3, x_4);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_10; 
x_10 = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(x_5, x_2, x_3, x_6);
lean_dec(x_3);
return x_10;
}
}
}
lean_object* l_Lean_Parser_rawFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Parser_rawFn(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Parser_chFn(uint32_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_5 = lean_box_uint32(x_1);
x_6 = lean_alloc_closure((void*)(l_UInt32_decEq___boxed), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = l_Lean_instInhabitedParserDescr___closed__1;
x_8 = lean_string_push(x_7, x_1);
x_9 = l_Char_quote___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_string_append(x_10, x_9);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = l_Lean_Parser_satisfyFn(x_6, x_11, x_3, x_4);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
x_15 = lean_box(0);
x_16 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_dec(x_12);
return x_13;
}
else
{
lean_object* x_17; 
x_17 = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(x_12, x_2, x_3, x_13);
return x_17;
}
}
}
lean_object* l_Lean_Parser_chFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Parser_chFn(x_5, x_6, x_3, x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Parser_rawCh___elambda__1(uint32_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_5 = lean_box_uint32(x_1);
x_6 = lean_alloc_closure((void*)(l_UInt32_decEq___boxed), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = l_Lean_instInhabitedParserDescr___closed__1;
x_8 = lean_string_push(x_7, x_1);
x_9 = l_Char_quote___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_string_append(x_10, x_9);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = l_Lean_Parser_satisfyFn(x_6, x_11, x_3, x_4);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
x_15 = lean_box(0);
x_16 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_dec(x_12);
return x_13;
}
else
{
lean_object* x_17; 
x_17 = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(x_12, x_2, x_3, x_13);
return x_17;
}
}
}
lean_object* l_Lean_Parser_rawCh(uint32_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_box_uint32(x_1);
x_4 = lean_box(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_rawCh___elambda__1___boxed), 4, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
x_6 = l_Lean_Parser_errorAtSavedPos___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_rawCh___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Parser_rawCh___elambda__1(x_5, x_6, x_3, x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Parser_rawCh___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Parser_rawCh(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_hexDigitFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid hexadecimal numeral");
return x_1;
}
}
lean_object* l_Lean_Parser_hexDigitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_at_end(x_4, x_5);
if (x_6 == 0)
{
uint32_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_20; 
x_7 = lean_string_utf8_get(x_4, x_5);
x_8 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
x_20 = l_Char_isDigit(x_7);
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; 
x_21 = 97;
x_22 = x_21 <= x_7;
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_box(0);
x_9 = x_23;
goto block_19;
}
else
{
uint32_t x_24; uint8_t x_25; 
x_24 = 102;
x_25 = x_7 <= x_24;
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_box(0);
x_9 = x_26;
goto block_19;
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Parser_ParserState_setPos(x_2, x_8);
return x_27;
}
}
}
else
{
lean_object* x_28; 
x_28 = l_Lean_Parser_ParserState_setPos(x_2, x_8);
return x_28;
}
block_19:
{
uint32_t x_10; uint8_t x_11; 
lean_dec(x_9);
x_10 = 65;
x_11 = x_10 <= x_7;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
x_12 = l_Lean_Parser_hexDigitFn___closed__1;
x_13 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_12);
return x_13;
}
else
{
uint32_t x_14; uint8_t x_15; 
x_14 = 70;
x_15 = x_7 <= x_14;
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
x_16 = l_Lean_Parser_hexDigitFn___closed__1;
x_17 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_16);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_Parser_ParserState_setPos(x_2, x_8);
return x_18;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_5);
x_29 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_30 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_29);
return x_30;
}
}
}
lean_object* l_Lean_Parser_hexDigitFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_hexDigitFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharCoreFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid escape sequence");
return x_1;
}
}
lean_object* l_Lean_Parser_quotedCharCoreFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_string_utf8_at_end(x_5, x_6);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_string_utf8_get(x_5, x_6);
x_9 = lean_box_uint32(x_8);
x_10 = lean_apply_1(x_1, x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 120;
x_13 = x_8 == x_12;
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 117;
x_15 = x_8 == x_14;
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
x_16 = l_Lean_Parser_quotedCharCoreFn___closed__1;
x_17 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = l_Lean_Parser_ParserState_next(x_3, x_5, x_6);
lean_dec(x_6);
x_19 = l_Lean_Parser_hexDigitFn(x_2, x_18);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
x_21 = lean_box(0);
x_22 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_20, x_21);
lean_dec(x_20);
if (x_22 == 0)
{
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Lean_Parser_hexDigitFn(x_2, x_19);
x_24 = lean_ctor_get(x_23, 3);
lean_inc(x_24);
x_25 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_24, x_21);
lean_dec(x_24);
if (x_25 == 0)
{
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = l_Lean_Parser_hexDigitFn(x_2, x_23);
x_27 = lean_ctor_get(x_26, 3);
lean_inc(x_27);
x_28 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_27, x_21);
lean_dec(x_27);
if (x_28 == 0)
{
return x_26;
}
else
{
lean_object* x_29; 
x_29 = l_Lean_Parser_hexDigitFn(x_2, x_26);
return x_29;
}
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = l_Lean_Parser_ParserState_next(x_3, x_5, x_6);
lean_dec(x_6);
x_31 = l_Lean_Parser_hexDigitFn(x_2, x_30);
x_32 = lean_ctor_get(x_31, 3);
lean_inc(x_32);
x_33 = lean_box(0);
x_34 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
return x_31;
}
else
{
lean_object* x_35; 
x_35 = l_Lean_Parser_hexDigitFn(x_2, x_31);
return x_35;
}
}
}
else
{
lean_object* x_36; 
x_36 = l_Lean_Parser_ParserState_next(x_3, x_5, x_6);
lean_dec(x_6);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_6);
lean_dec(x_1);
x_37 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_38 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_37);
return x_38;
}
}
}
lean_object* l_Lean_Parser_quotedCharCoreFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_quotedCharCoreFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 92;
x_3 = x_1 == x_2;
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 34;
x_5 = x_1 == x_4;
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 39;
x_7 = x_1 == x_6;
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 114;
x_9 = x_1 == x_8;
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 110;
x_11 = x_1 == x_10;
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 116;
x_13 = x_1 == x_12;
return x_13;
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
lean_object* l_Lean_Parser_isQuotableCharDefault___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_isQuotableCharDefault(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_isQuotableCharDefault___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_quotedCharFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_quotedCharFn___closed__1;
x_4 = l_Lean_Parser_quotedCharCoreFn(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_quotedCharFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_quotedCharFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_mkNodeToken(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc_n(x_2, 2);
lean_inc(x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_2);
x_9 = lean_string_utf8_extract(x_6, x_2, x_7);
x_10 = l_Lean_Parser_whitespace(x_3, x_4);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_inc(x_6);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = l_Lean_Syntax_mkLit(x_1, x_9, x_16);
x_18 = l_Lean_Parser_ParserState_pushSyntax(x_10, x_17);
return x_18;
}
}
lean_object* l_Lean_Parser_mkNodeToken___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_mkNodeToken(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_charLitFnAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("missing end of character literal");
return x_1;
}
}
lean_object* l_Lean_Parser_charLitFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_string_utf8_at_end(x_5, x_6);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; lean_object* x_13; 
x_8 = lean_string_utf8_get(x_5, x_6);
x_9 = lean_string_utf8_next(x_5, x_6);
lean_dec(x_6);
lean_inc(x_9);
lean_inc(x_3);
x_10 = l_Lean_Parser_ParserState_setPos(x_3, x_9);
x_11 = 92;
x_12 = x_8 == x_11;
x_13 = lean_box(0);
if (x_12 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_3, 3);
lean_inc(x_14);
lean_dec(x_3);
x_15 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_14, x_13);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_9);
lean_dec(x_1);
return x_10;
}
else
{
uint32_t x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; uint8_t x_20; 
x_16 = lean_string_utf8_get(x_5, x_9);
x_17 = lean_string_utf8_next(x_5, x_9);
lean_dec(x_9);
x_18 = l_Lean_Parser_ParserState_setPos(x_10, x_17);
x_19 = 39;
x_20 = x_16 == x_19;
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_21 = l_Lean_Parser_charLitFnAux___closed__1;
x_22 = l_Lean_Parser_ParserState_mkUnexpectedError(x_18, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_charLitKind;
x_24 = l_Lean_Parser_mkNodeToken(x_23, x_1, x_2, x_18);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_3);
x_25 = l_Lean_Parser_quotedCharFn___closed__1;
x_26 = l_Lean_Parser_quotedCharCoreFn(x_25, x_2, x_10);
x_27 = lean_ctor_get(x_26, 3);
lean_inc(x_27);
x_28 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_27, x_13);
lean_dec(x_27);
if (x_28 == 0)
{
lean_dec(x_1);
return x_26;
}
else
{
lean_object* x_29; uint32_t x_30; lean_object* x_31; lean_object* x_32; uint32_t x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = lean_string_utf8_get(x_5, x_29);
x_31 = lean_string_utf8_next(x_5, x_29);
lean_dec(x_29);
x_32 = l_Lean_Parser_ParserState_setPos(x_26, x_31);
x_33 = 39;
x_34 = x_30 == x_33;
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_1);
x_35 = l_Lean_Parser_charLitFnAux___closed__1;
x_36 = l_Lean_Parser_ParserState_mkUnexpectedError(x_32, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_charLitKind;
x_38 = l_Lean_Parser_mkNodeToken(x_37, x_1, x_2, x_32);
return x_38;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_6);
lean_dec(x_1);
x_39 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_40 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_39);
return x_40;
}
}
}
lean_object* l_Lean_Parser_charLitFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_charLitFnAux(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_strLitFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_string_utf8_at_end(x_5, x_6);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; 
x_8 = lean_string_utf8_get(x_5, x_6);
x_9 = lean_string_utf8_next(x_5, x_6);
lean_dec(x_6);
x_10 = l_Lean_Parser_ParserState_setPos(x_3, x_9);
x_11 = 34;
x_12 = x_8 == x_11;
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 92;
x_14 = x_8 == x_13;
if (x_14 == 0)
{
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = l_Lean_Parser_quotedCharFn___closed__1;
x_17 = l_Lean_Parser_quotedCharCoreFn(x_16, x_2, x_10);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
x_19 = lean_box(0);
x_20 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_dec(x_1);
return x_17;
}
else
{
x_3 = x_17;
goto _start;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_strLitKind;
x_23 = l_Lean_Parser_mkNodeToken(x_22, x_1, x_2, x_10);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_1);
x_24 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_25 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_24);
return x_25;
}
}
}
lean_object* l_Lean_Parser_strLitFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_strLitFnAux(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_isDigit___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_decimalNumberFn_parseOptDot(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_get(x_4, x_5);
x_7 = 46;
x_8 = x_6 == x_7;
if (x_8 == 0)
{
lean_dec(x_5);
return x_2;
}
else
{
lean_object* x_9; uint32_t x_10; uint8_t x_11; 
x_9 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
x_10 = lean_string_utf8_get(x_4, x_9);
x_11 = l_Char_isDigit(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Parser_ParserState_setPos(x_2, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Parser_ParserState_setPos(x_2, x_9);
x_14 = l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1;
x_15 = l_Lean_Parser_takeWhileFn(x_14, x_1, x_13);
return x_15;
}
}
}
}
lean_object* l_Lean_Parser_decimalNumberFn_parseOptDot___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_decimalNumberFn_parseOptDot(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint32_t x_24; uint32_t x_25; uint8_t x_26; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_24 = lean_string_utf8_get(x_4, x_5);
x_25 = 101;
x_26 = x_24 == x_25;
if (x_26 == 0)
{
uint32_t x_27; uint8_t x_28; 
x_27 = 69;
x_28 = x_24 == x_27;
if (x_28 == 0)
{
lean_dec(x_5);
return x_2;
}
else
{
lean_object* x_29; 
x_29 = lean_box(0);
x_6 = x_29;
goto block_23;
}
}
else
{
lean_object* x_30; 
x_30 = lean_box(0);
x_6 = x_30;
goto block_23;
}
block_23:
{
lean_object* x_7; uint32_t x_8; uint32_t x_9; uint8_t x_10; 
lean_dec(x_6);
x_7 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
x_8 = lean_string_utf8_get(x_4, x_7);
x_9 = 45;
x_10 = x_8 == x_9;
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Char_isDigit(x_8);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Parser_ParserState_setPos(x_2, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Parser_ParserState_setPos(x_2, x_7);
x_14 = l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1;
x_15 = l_Lean_Parser_takeWhileFn(x_14, x_1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_16 = lean_string_utf8_next(x_4, x_7);
lean_dec(x_7);
x_17 = lean_string_utf8_get(x_4, x_16);
x_18 = l_Char_isDigit(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_Parser_ParserState_setPos(x_2, x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_Parser_ParserState_setPos(x_2, x_16);
x_21 = l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1;
x_22 = l_Lean_Parser_takeWhileFn(x_21, x_1, x_20);
return x_22;
}
}
}
}
}
lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_decimalNumberFn_parseOptExp(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_decimalNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_4 = l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1;
x_5 = l_Lean_Parser_takeWhileFn(x_4, x_2, x_3);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_string_utf8_get(x_7, x_8);
lean_dec(x_8);
x_10 = 46;
x_11 = x_9 == x_10;
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 101;
x_13 = x_9 == x_12;
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 69;
x_15 = x_9 == x_14;
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_numLitKind;
x_17 = l_Lean_Parser_mkNodeToken(x_16, x_1, x_2, x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l_Lean_Parser_decimalNumberFn_parseOptDot(x_2, x_5);
x_19 = l_Lean_Parser_decimalNumberFn_parseOptExp(x_2, x_18);
x_20 = l_Lean_scientificLitKind;
x_21 = l_Lean_Parser_mkNodeToken(x_20, x_1, x_2, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = l_Lean_Parser_decimalNumberFn_parseOptDot(x_2, x_5);
x_23 = l_Lean_Parser_decimalNumberFn_parseOptExp(x_2, x_22);
x_24 = l_Lean_scientificLitKind;
x_25 = l_Lean_Parser_mkNodeToken(x_24, x_1, x_2, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = l_Lean_Parser_decimalNumberFn_parseOptDot(x_2, x_5);
x_27 = l_Lean_Parser_decimalNumberFn_parseOptExp(x_2, x_26);
x_28 = l_Lean_scientificLitKind;
x_29 = l_Lean_Parser_mkNodeToken(x_28, x_1, x_2, x_27);
return x_29;
}
}
}
lean_object* l_Lean_Parser_decimalNumberFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_decimalNumberFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
uint8_t l_Lean_Parser_binNumberFn___lambda__1(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 48;
x_3 = x_1 == x_2;
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 49;
x_5 = x_1 == x_4;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
}
static lean_object* _init_l_Lean_Parser_binNumberFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_binNumberFn___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_binNumberFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("binary number");
return x_1;
}
}
lean_object* l_Lean_Parser_binNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l_Lean_Parser_binNumberFn___closed__1;
x_5 = l_Lean_Parser_binNumberFn___closed__2;
x_6 = l_Lean_Parser_satisfyFn(x_4, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_numLitKind;
x_11 = l_Lean_Parser_mkNodeToken(x_10, x_1, x_2, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Parser_takeWhileFn(x_4, x_2, x_6);
x_13 = l_Lean_numLitKind;
x_14 = l_Lean_Parser_mkNodeToken(x_13, x_1, x_2, x_12);
return x_14;
}
}
}
lean_object* l_Lean_Parser_binNumberFn___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_binNumberFn___lambda__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_binNumberFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_binNumberFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
uint8_t l_Lean_Parser_octalNumberFn___lambda__1(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 48;
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
x_5 = 55;
x_6 = x_1 <= x_5;
return x_6;
}
}
}
static lean_object* _init_l_Lean_Parser_octalNumberFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_octalNumberFn___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_octalNumberFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("octal number");
return x_1;
}
}
lean_object* l_Lean_Parser_octalNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l_Lean_Parser_octalNumberFn___closed__1;
x_5 = l_Lean_Parser_octalNumberFn___closed__2;
x_6 = l_Lean_Parser_satisfyFn(x_4, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_numLitKind;
x_11 = l_Lean_Parser_mkNodeToken(x_10, x_1, x_2, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Parser_takeWhileFn(x_4, x_2, x_6);
x_13 = l_Lean_numLitKind;
x_14 = l_Lean_Parser_mkNodeToken(x_13, x_1, x_2, x_12);
return x_14;
}
}
}
lean_object* l_Lean_Parser_octalNumberFn___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_octalNumberFn___lambda__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_octalNumberFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_octalNumberFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
uint8_t l_Lean_Parser_hexNumberFn___lambda__1(uint32_t x_1) {
_start:
{
lean_object* x_2; uint32_t x_19; uint8_t x_20; 
x_19 = 48;
x_20 = x_19 <= x_1;
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_box(0);
x_2 = x_21;
goto block_18;
}
else
{
uint32_t x_22; uint8_t x_23; 
x_22 = 57;
x_23 = x_1 <= x_22;
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_box(0);
x_2 = x_24;
goto block_18;
}
else
{
uint8_t x_25; 
x_25 = 1;
return x_25;
}
}
block_18:
{
uint32_t x_3; uint8_t x_4; 
lean_dec(x_2);
x_3 = 97;
x_4 = x_3 <= x_1;
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 65;
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
x_8 = 70;
x_9 = x_1 <= x_8;
return x_9;
}
}
else
{
uint32_t x_10; uint8_t x_11; 
x_10 = 102;
x_11 = x_1 <= x_10;
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 65;
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
x_15 = 70;
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
static lean_object* _init_l_Lean_Parser_hexNumberFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_hexNumberFn___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_hexNumberFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hexadecimal number");
return x_1;
}
}
lean_object* l_Lean_Parser_hexNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l_Lean_Parser_hexNumberFn___closed__1;
x_5 = l_Lean_Parser_hexNumberFn___closed__2;
x_6 = l_Lean_Parser_satisfyFn(x_4, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_numLitKind;
x_11 = l_Lean_Parser_mkNodeToken(x_10, x_1, x_2, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Parser_takeWhileFn(x_4, x_2, x_6);
x_13 = l_Lean_numLitKind;
x_14 = l_Lean_Parser_mkNodeToken(x_13, x_1, x_2, x_12);
return x_14;
}
}
}
lean_object* l_Lean_Parser_hexNumberFn___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_hexNumberFn___lambda__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_hexNumberFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_hexNumberFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_numberFnAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("numeral");
return x_1;
}
}
lean_object* l_Lean_Parser_numberFnAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_at_end(x_4, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_7 = lean_string_utf8_get(x_4, x_5);
x_8 = 48;
x_9 = x_7 == x_8;
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Char_isDigit(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = l_Lean_Parser_numberFnAux___closed__1;
x_12 = l_Lean_Parser_ParserState_mkError(x_2, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
x_14 = l_Lean_Parser_decimalNumberFn(x_5, x_1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; uint32_t x_16; uint32_t x_17; uint8_t x_18; 
x_15 = lean_string_utf8_next(x_4, x_5);
x_16 = lean_string_utf8_get(x_4, x_15);
x_17 = 98;
x_18 = x_16 == x_17;
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 66;
x_20 = x_16 == x_19;
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; 
x_21 = 111;
x_22 = x_16 == x_21;
if (x_22 == 0)
{
uint32_t x_23; uint8_t x_24; 
x_23 = 79;
x_24 = x_16 == x_23;
if (x_24 == 0)
{
uint32_t x_25; uint8_t x_26; 
x_25 = 120;
x_26 = x_16 == x_25;
if (x_26 == 0)
{
uint32_t x_27; uint8_t x_28; 
x_27 = 88;
x_28 = x_16 == x_27;
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Parser_ParserState_setPos(x_2, x_15);
x_30 = l_Lean_Parser_decimalNumberFn(x_5, x_1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_Parser_ParserState_next(x_2, x_4, x_15);
lean_dec(x_15);
x_32 = l_Lean_Parser_hexNumberFn(x_5, x_1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_Parser_ParserState_next(x_2, x_4, x_15);
lean_dec(x_15);
x_34 = l_Lean_Parser_hexNumberFn(x_5, x_1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_Parser_ParserState_next(x_2, x_4, x_15);
lean_dec(x_15);
x_36 = l_Lean_Parser_octalNumberFn(x_5, x_1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_Parser_ParserState_next(x_2, x_4, x_15);
lean_dec(x_15);
x_38 = l_Lean_Parser_octalNumberFn(x_5, x_1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_Parser_ParserState_next(x_2, x_4, x_15);
lean_dec(x_15);
x_40 = l_Lean_Parser_binNumberFn(x_5, x_1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_Parser_ParserState_next(x_2, x_4, x_15);
lean_dec(x_15);
x_42 = l_Lean_Parser_binNumberFn(x_5, x_1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_5);
x_43 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_44 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_43);
return x_44;
}
}
}
lean_object* l_Lean_Parser_numberFnAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_numberFnAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l_Lean_Parser_isIdCont(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; uint32_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_string_utf8_get(x_1, x_3);
x_5 = 46;
x_6 = x_4 == x_5;
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_string_utf8_next(x_1, x_3);
x_9 = lean_string_utf8_at_end(x_1, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = lean_string_utf8_get(x_1, x_8);
lean_dec(x_8);
x_11 = l_Lean_isIdFirst(x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = l_Lean_idBeginEscape;
x_13 = x_10 == x_12;
return x_13;
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
lean_dec(x_8);
x_15 = 0;
return x_15;
}
}
}
}
lean_object* l_Lean_Parser_isIdCont___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_isIdCont(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_isToken_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_nat_sub(x_2, x_1);
x_7 = lean_string_utf8_byte_size(x_5);
x_8 = lean_nat_dec_le(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_mkTokenAndFixPos_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_mkTokenAndFixPos_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_mkTokenAndFixPos_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_mkTokenAndFixPos___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_string_dec_eq(x_6, x_7);
return x_8;
}
}
}
}
static lean_object* _init_l_Lean_Parser_mkTokenAndFixPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("token");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkTokenAndFixPos___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("forbidden token");
return x_1;
}
}
lean_object* l_Lean_Parser_mkTokenAndFixPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parser_mkTokenAndFixPos___closed__1;
x_6 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_5, x_1);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_3, 5);
lean_inc(x_8);
x_10 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_mkTokenAndFixPos___spec__1(x_9, x_2);
lean_dec(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_n(x_1, 2);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_13, 2, x_1);
x_14 = lean_string_utf8_byte_size(x_8);
x_15 = lean_nat_add(x_1, x_14);
lean_dec(x_14);
lean_inc(x_15);
x_16 = l_Lean_Parser_ParserState_setPos(x_4, x_15);
x_17 = l_Lean_Parser_whitespace(x_3, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_inc(x_12);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_13);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_8);
x_25 = l_Lean_Parser_ParserState_pushSyntax(x_17, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_8);
x_26 = l_Lean_Parser_mkTokenAndFixPos___closed__2;
x_27 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_26, x_1);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_ctor_get(x_3, 5);
lean_inc(x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_mkTokenAndFixPos___spec__1(x_29, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_32 = lean_ctor_get(x_3, 0);
x_33 = lean_ctor_get(x_32, 0);
lean_inc_n(x_1, 2);
lean_inc(x_33);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_1);
lean_ctor_set(x_34, 2, x_1);
x_35 = lean_string_utf8_byte_size(x_28);
x_36 = lean_nat_add(x_1, x_35);
lean_dec(x_35);
lean_inc(x_36);
x_37 = l_Lean_Parser_ParserState_setPos(x_4, x_36);
x_38 = l_Lean_Parser_whitespace(x_3, x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_inc(x_33);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_34);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_1);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_43);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_28);
x_46 = l_Lean_Parser_ParserState_pushSyntax(x_38, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_28);
x_47 = l_Lean_Parser_mkTokenAndFixPos___closed__2;
x_48 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_47, x_1);
return x_48;
}
}
}
}
}
lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_mkTokenAndFixPos___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_mkTokenAndFixPos___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_mkTokenAndFixPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_mkTokenAndFixPos(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_mkIdResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(x_1, x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_1);
lean_ctor_set(x_10, 2, x_6);
x_11 = l_Lean_Parser_whitespace(x_4, x_5);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_inc_n(x_1, 2);
lean_inc(x_9);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_13, 2, x_1);
lean_inc(x_9);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_20, 2, x_3);
lean_ctor_set(x_20, 3, x_19);
x_21 = l_Lean_Parser_ParserState_pushSyntax(x_11, x_20);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_3);
x_22 = l_Lean_Parser_mkTokenAndFixPos(x_1, x_2, x_4, x_5);
return x_22;
}
}
}
lean_object* l_Lean_Parser_mkIdResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_mkIdResult(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_identFnAux_parse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_isIdRest___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_identFnAux_parse___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_isIdEndEscape___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_identFnAux_parse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("missing end of escaped identifier");
return x_1;
}
}
lean_object* l_Lean_Parser_identFnAux_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_string_utf8_at_end(x_7, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_10 = lean_string_utf8_get(x_7, x_8);
x_11 = l_Lean_idBeginEscape;
x_12 = x_10 == x_11;
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_isIdFirst(x_10);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_3);
x_14 = l_Lean_Parser_mkTokenAndFixPos(x_1, x_2, x_4, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = l_Lean_Parser_ParserState_next(x_5, x_7, x_8);
x_16 = l_Lean_Parser_identFnAux_parse___closed__1;
x_17 = l_Lean_Parser_takeWhileFn(x_16, x_4, x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_string_utf8_extract(x_7, x_8, x_18);
lean_dec(x_8);
x_20 = lean_name_mk_string(x_3, x_19);
x_21 = l_Lean_Parser_isIdCont(x_7, x_17);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
x_22 = l_Lean_Parser_mkIdResult(x_1, x_2, x_20, x_4, x_17);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = l_Lean_Parser_ParserState_next(x_17, x_7, x_18);
lean_dec(x_18);
x_3 = x_20;
x_5 = x_23;
goto _start;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_25 = lean_string_utf8_next(x_7, x_8);
lean_dec(x_8);
lean_inc(x_25);
x_26 = l_Lean_Parser_ParserState_setPos(x_5, x_25);
x_27 = l_Lean_Parser_identFnAux_parse___closed__2;
x_28 = l_Lean_Parser_takeUntilFn(x_27, x_4, x_26);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = l_Lean_Parser_identFnAux_parse___closed__3;
x_31 = l_Lean_Parser_satisfyFn(x_27, x_30, x_4, x_28);
x_32 = lean_ctor_get(x_31, 3);
lean_inc(x_32);
x_33 = lean_box(0);
x_34 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_string_utf8_extract(x_7, x_25, x_29);
lean_dec(x_29);
lean_dec(x_25);
x_36 = lean_name_mk_string(x_3, x_35);
x_37 = l_Lean_Parser_isIdCont(x_7, x_31);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = l_Lean_Parser_mkIdResult(x_1, x_2, x_36, x_4, x_31);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
x_40 = l_Lean_Parser_ParserState_next(x_31, x_7, x_39);
lean_dec(x_39);
x_3 = x_36;
x_5 = x_40;
goto _start;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_43 = l_Lean_Parser_ParserState_mkUnexpectedError(x_5, x_42);
return x_43;
}
}
}
lean_object* l_Lean_Parser_identFnAux_parse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_identFnAux_parse(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Parser_identFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_identFnAux_parse(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_identFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_identFnAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(uint32_t x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_isIdFirst(x_1);
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = l_Lean_idBeginEscape;
x_4 = x_1 == x_3;
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
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid Name literal");
return x_1;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_box(0);
x_7 = l_Lean_Parser_ParserState_next(x_3, x_5, x_1);
x_8 = lean_box(0);
lean_inc(x_1);
x_9 = l_Lean_Parser_identFnAux_parse(x_1, x_6, x_8, x_2, x_7);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
x_11 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_10, x_6);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__1;
x_13 = l_Lean_Parser_ParserState_mkErrorAt(x_9, x_12, x_1);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
x_15 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 3)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = l_Lean_Parser_ParserState_popSyntax(x_9);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_string_utf8_extract(x_18, x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_22 = l_Lean_mkAtomFrom(x_15, x_21);
lean_dec(x_15);
x_23 = l_Lean_mkOptionalNode___closed__2;
x_24 = lean_array_push(x_23, x_22);
x_25 = l_Lean_nameLitKind;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Parser_ParserState_pushSyntax(x_17, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_15);
x_28 = l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__1;
x_29 = l_Lean_Parser_ParserState_mkError(x_9, x_28);
return x_29;
}
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_get(x_4, x_5);
x_7 = 34;
x_8 = x_6 == x_7;
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 39;
x_10 = x_6 == x_9;
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Char_isDigit(x_6);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 96;
x_13 = x_6 == x_12;
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_inc(x_5);
x_15 = l_Lean_Parser_Trie_matchPrefix___rarg(x_4, x_14, x_5);
lean_dec(x_4);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Parser_identFnAux_parse(x_5, x_16, x_17, x_1, x_2);
lean_dec(x_1);
return x_18;
}
else
{
uint32_t x_19; uint8_t x_20; 
x_19 = l_Lean_Parser_getNext(x_4, x_5);
x_20 = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_inc(x_5);
x_22 = l_Lean_Parser_Trie_matchPrefix___rarg(x_4, x_21, x_5);
lean_dec(x_4);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = l_Lean_Parser_identFnAux_parse(x_5, x_23, x_24, x_1, x_2);
lean_dec(x_1);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_4);
x_26 = l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(x_5, x_1, x_2);
lean_dec(x_1);
return x_26;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_5);
lean_dec(x_4);
x_27 = l_Lean_Parser_numberFnAux(x_1, x_2);
lean_dec(x_1);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_4);
x_29 = l_Lean_Parser_charLitFnAux(x_5, x_1, x_28);
lean_dec(x_1);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_4);
x_31 = l_Lean_Parser_strLitFnAux(x_5, x_1, x_30);
lean_dec(x_1);
return x_31;
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateCache_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_3(x_2, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateCache_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_updateCache_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateCache(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_array_get_size(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_2, 3);
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
x_14 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_4);
lean_inc(x_5);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_box(0);
lean_ctor_set(x_2, 3, x_16);
lean_ctor_set(x_2, 2, x_15);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_17 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_4);
lean_inc(x_5);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_5);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_19);
return x_20;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
}
lean_object* l_Lean_Parser_tokenFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_at_end(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_nat_dec_eq(x_8, x_5);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(x_1, x_2);
x_11 = l___private_Lean_Parser_Basic_0__Lean_Parser_updateCache(x_5, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
x_13 = l_Lean_Parser_ParserState_pushSyntax(x_2, x_12);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = l_Lean_Parser_ParserState_setPos(x_13, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_1);
x_16 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_17 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_16);
return x_17;
}
}
}
lean_object* l_Lean_Parser_peekTokenAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = l_Lean_Parser_tokenFn(x_1, x_2);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_12);
lean_dec(x_12);
x_14 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
lean_object* l_Lean_Parser_peekToken(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = l_Lean_Parser_peekTokenAux(x_1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Parser_rawIdentFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_at_end(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = l_Lean_Parser_identFnAux_parse(x_5, x_7, x_8, x_1, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_10 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_11 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Parser_rawIdentFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_rawIdentFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_satisfySymbolFn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_satisfySymbolFn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_satisfySymbolFn_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_satisfySymbolFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = l_Lean_Parser_tokenFn(x_3, x_4);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_2, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 2)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_1(x_1, x_13);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_2, x_5);
return x_16;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_1);
x_17 = l_Lean_Parser_ParserState_mkErrorsAt(x_6, x_2, x_5);
return x_17;
}
}
}
}
lean_object* l_Lean_Parser_symbolFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = l_Lean_Parser_tokenFn(x_3, x_4);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Parser_ParserState_mkErrorsAt(x_8, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 2)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_string_dec_eq(x_15, x_1);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Parser_ParserState_mkErrorsAt(x_8, x_6, x_7);
return x_17;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
}
else
{
lean_object* x_18; 
lean_dec(x_14);
x_18 = l_Lean_Parser_ParserState_mkErrorsAt(x_8, x_6, x_7);
return x_18;
}
}
}
}
lean_object* l_Lean_Parser_symbolFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_symbolFnAux(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Parser_symbolInfo___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_symbolInfo___elambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_symbolInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_symbolInfo___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_symbolInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbolInfo___elambda__2), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_Parser_symbolInfo___closed__1;
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_symbolInfo___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_symbolInfo___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_symbolFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Char_quote___closed__1;
x_5 = lean_string_append(x_4, x_1);
x_6 = lean_string_append(x_5, x_4);
x_7 = l_Lean_Parser_symbolFnAux(x_1, x_6, x_2, x_3);
return x_7;
}
}
lean_object* l_Lean_Parser_symbolFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_symbolFn(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_symbol(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_String_trim(x_1);
lean_inc(x_2);
x_3 = l_Lean_Parser_symbolInfo(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_symbol___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_symbol(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_nonReservedSymbolFnAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Parser_nonReservedSymbolFnAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolFnAux_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = l_Lean_Parser_tokenFn(x_3, x_4);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_Parser_ParserState_mkErrorAt(x_6, x_2, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_11);
lean_dec(x_11);
switch (lean_obj_tag(x_12)) {
case 2:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_string_dec_eq(x_1, x_13);
lean_dec(x_13);
lean_dec(x_1);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Parser_ParserState_mkErrorAt(x_6, x_2, x_5);
return x_15;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
case 3:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_string_utf8_extract(x_18, x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_22 = lean_string_dec_eq(x_1, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_17);
lean_dec(x_1);
x_23 = l_Lean_Parser_ParserState_mkErrorAt(x_6, x_2, x_5);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
lean_dec(x_2);
x_24 = l_Lean_Parser_ParserState_popSyntax(x_6);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_1);
x_26 = l_Lean_Parser_ParserState_pushSyntax(x_24, x_25);
return x_26;
}
}
default: 
{
lean_object* x_27; 
lean_dec(x_12);
lean_dec(x_1);
x_27 = l_Lean_Parser_ParserState_mkErrorAt(x_6, x_2, x_5);
return x_27;
}
}
}
}
}
lean_object* l_Lean_Parser_nonReservedSymbolFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Char_quote___closed__1;
x_5 = lean_string_append(x_4, x_1);
x_6 = lean_string_append(x_5, x_4);
x_7 = l_Lean_Parser_nonReservedSymbolFnAux(x_1, x_6, x_2, x_3);
return x_7;
}
}
lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__2(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_nonReservedSymbolInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolInfo___elambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_nonReservedSymbolInfo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolInfo___elambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_nonReservedSymbolInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_identKind___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object* x_1, uint8_t x_2) {
_start:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_Parser_nonReservedSymbolInfo___closed__1;
x_7 = l_Lean_Parser_nonReservedSymbolInfo___closed__2;
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_Parser_nonReservedSymbolInfo___closed__3;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_Parser_nonReservedSymbolInfo___closed__1;
x_13 = l_Lean_Parser_nonReservedSymbolInfo___closed__2;
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_11);
return x_14;
}
}
}
lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_nonReservedSymbolInfo___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_nonReservedSymbolInfo___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_nonReservedSymbolInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_nonReservedSymbol(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_String_trim(x_1);
lean_inc(x_3);
x_4 = l_Lean_Parser_nonReservedSymbolInfo(x_3, x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolFn), 3, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_nonReservedSymbol___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Parser_nonReservedSymbol(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_strAux_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_8, 0);
x_10 = lean_string_utf8_at_end(x_9, x_7);
if (x_10 == 0)
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_string_utf8_get(x_1, x_3);
x_12 = lean_string_utf8_get(x_9, x_7);
x_13 = x_11 == x_12;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_3);
x_14 = l_Lean_Parser_ParserState_mkError(x_5, x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_16 = l_Lean_Parser_ParserState_next(x_5, x_9, x_7);
lean_dec(x_7);
x_3 = x_15;
x_5 = x_16;
goto _start;
}
}
else
{
lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_3);
x_18 = l_Lean_Parser_ParserState_mkError(x_5, x_2);
return x_18;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
}
lean_object* l_Lean_Parser_strAux_parse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_strAux_parse(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Parser_strAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_strAux_parse(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_strAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_strAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Parser_checkTailWs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_apply_3(x_2, x_10, x_8, x_9);
return x_11;
}
}
}
}
lean_object* l_Lean_Parser_checkTailWs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkTailWs_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Parser_checkTailWs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
return x_10;
}
}
}
}
lean_object* l_Lean_Parser_checkTailWs___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_checkTailWs(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_checkWsBeforeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_checkTailWs(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_7;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l_Lean_Parser_checkWsBeforeFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkWsBeforeFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_checkWsBefore___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkWsBeforeFn(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_checkWsBefore(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkWsBefore___elambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_epsilonInfo;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_checkWsBefore___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkWsBefore___elambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_checkTailNoWs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_apply_3(x_2, x_10, x_8, x_9);
return x_11;
}
}
}
}
lean_object* l_Lean_Parser_checkTailNoWs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkTailNoWs_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Parser_checkTailNoWs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
return x_10;
}
}
}
}
lean_object* l_Lean_Parser_checkTailNoWs___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_checkTailNoWs(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_findSomeRevM_x3f_find___at___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_8 = lean_array_fget(x_1, x_7);
x_9 = l_Lean_Syntax_isNone(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_dec(x_8);
x_2 = x_7;
x_3 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_box(0);
return x_12;
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_array_get_size(x_1);
x_3 = l_Array_findSomeRevM_x3f_find___at___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___spec__1(x_1, x_2, lean_box(0));
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
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
lean_object* l_Array_findSomeRevM_x3f_find___at___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findSomeRevM_x3f_find___at___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_checkTailNoWs(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_7;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l_Lean_Parser_checkNoWsBeforeFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkNoWsBeforeFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_checkNoWsBefore___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkNoWsBeforeFn(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_checkNoWsBefore(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkNoWsBefore___elambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_epsilonInfo;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_checkNoWsBefore___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkNoWsBefore___elambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = l_Lean_Parser_tokenFn(x_4, x_5);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Parser_ParserState_mkErrorsAt(x_7, x_3, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 2)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_string_dec_eq(x_14, x_1);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = lean_string_dec_eq(x_14, x_2);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Parser_ParserState_mkErrorsAt(x_7, x_3, x_6);
return x_17;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
return x_7;
}
}
else
{
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_3);
return x_7;
}
}
else
{
lean_object* x_18; 
lean_dec(x_13);
x_18 = l_Lean_Parser_ParserState_mkErrorsAt(x_7, x_3, x_6);
return x_18;
}
}
}
}
lean_object* l_Lean_Parser_unicodeSymbolFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_unicodeSymbolFnAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_unicodeSymbolInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolInfo___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_unicodeSymbolInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolInfo___elambda__2), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_Parser_unicodeSymbolInfo___closed__1;
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_7);
return x_9;
}
}
lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_unicodeSymbolInfo___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_unicodeSymbolFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', '");
return x_1;
}
}
lean_object* l_Lean_Parser_unicodeSymbolFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l_Char_quote___closed__1;
x_6 = lean_string_append(x_5, x_1);
x_7 = l_Lean_Parser_unicodeSymbolFn___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_string_append(x_8, x_2);
x_10 = lean_string_append(x_9, x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_unicodeSymbolFnAux(x_1, x_2, x_12, x_3, x_4);
return x_13;
}
}
lean_object* l_Lean_Parser_unicodeSymbolFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_unicodeSymbolFn(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Parser_unicodeSymbol(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_String_trim(x_1);
x_4 = l_String_trim(x_2);
lean_inc(x_4);
lean_inc(x_3);
x_5 = l_Lean_Parser_unicodeSymbolInfo(x_3, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFn___boxed), 4, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_unicodeSymbol___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_unicodeSymbol(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_mkAtomicInfo___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_mkAtomicInfo___elambda__2(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAtomicInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_mkAtomicInfo___elambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAtomicInfo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_mkAtomicInfo___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_mkAtomicInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_Parser_mkAtomicInfo___closed__1;
x_6 = l_Lean_Parser_mkAtomicInfo___closed__2;
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_4);
return x_7;
}
}
lean_object* l_Lean_Parser_mkAtomicInfo___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_mkAtomicInfo___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_mkAtomicInfo___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_mkAtomicInfo___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_numLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_Parser_tokenFn(x_1, x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Parser_numberFnAux___closed__1;
x_9 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_8, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_10);
lean_dec(x_10);
x_12 = l_Lean_numLitKind;
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Parser_numberFnAux___closed__1;
x_15 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_14, x_3);
return x_15;
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_numLitKind___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_numLitFn), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_numLitNoAntiquot___closed__1;
x_2 = l_Lean_Parser_numLitNoAntiquot___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_numLitNoAntiquot___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("scientific number");
return x_1;
}
}
lean_object* l_Lean_Parser_scientificLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_Parser_tokenFn(x_1, x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Parser_scientificLitFn___closed__1;
x_9 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_8, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_10);
lean_dec(x_10);
x_12 = l_Lean_scientificLitKind;
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Parser_scientificLitFn___closed__1;
x_15 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_14, x_3);
return x_15;
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_scientificLitKind___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_scientificLitFn), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_scientificLitNoAntiquot___closed__1;
x_2 = l_Lean_Parser_scientificLitNoAntiquot___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_scientificLitNoAntiquot___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_strLitFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("string literal");
return x_1;
}
}
lean_object* l_Lean_Parser_strLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_Parser_tokenFn(x_1, x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Parser_strLitFn___closed__1;
x_9 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_8, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_10);
lean_dec(x_10);
x_12 = l_Lean_strLitKind;
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Parser_strLitFn___closed__1;
x_15 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_14, x_3);
return x_15;
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_strLitKind___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_strLitFn), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_strLitNoAntiquot___closed__1;
x_2 = l_Lean_Parser_strLitNoAntiquot___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_strLitNoAntiquot___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_charLitFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("character literal");
return x_1;
}
}
lean_object* l_Lean_Parser_charLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_Parser_tokenFn(x_1, x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Parser_charLitFn___closed__1;
x_9 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_8, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_10);
lean_dec(x_10);
x_12 = l_Lean_charLitKind;
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Parser_charLitFn___closed__1;
x_15 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_14, x_3);
return x_15;
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_charLitKind___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_charLitFn), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_charLitNoAntiquot___closed__1;
x_2 = l_Lean_Parser_charLitNoAntiquot___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_charLitNoAntiquot___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_nameLitFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Name literal");
return x_1;
}
}
lean_object* l_Lean_Parser_nameLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_Parser_tokenFn(x_1, x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Parser_nameLitFn___closed__1;
x_9 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_8, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_10);
lean_dec(x_10);
x_12 = l_Lean_nameLitKind;
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Parser_nameLitFn___closed__1;
x_15 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_14, x_3);
return x_15;
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_nameLitKind___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_nameLitFn), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_nameLitNoAntiquot___closed__1;
x_2 = l_Lean_Parser_nameLitNoAntiquot___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_nameLitNoAntiquot___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_identFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("identifier");
return x_1;
}
}
lean_object* l_Lean_Parser_identFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_Parser_tokenFn(x_1, x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Parser_identFn___closed__1;
x_9 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_8, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_10);
lean_dec(x_10);
x_12 = l_Lean_Syntax_isIdent(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Parser_identFn___closed__1;
x_14 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_13, x_3);
return x_14;
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_identKind___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_identFn), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_identNoAntiquot___closed__1;
x_2 = l_Lean_Parser_identNoAntiquot___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_identNoAntiquot___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_rawIdentNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_rawIdentFn___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_rawIdentNoAntiquot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_errorAtSavedPos___closed__1;
x_2 = l_Lean_Parser_rawIdentNoAntiquot___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_rawIdentNoAntiquot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_rawIdentNoAntiquot___closed__2;
return x_1;
}
}
lean_object* l_Lean_Parser_identEqFn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_identEqFn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_identEqFn_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_identEqFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected identifier '");
return x_1;
}
}
lean_object* l_Lean_Parser_identEqFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = l_Lean_Parser_tokenFn(x_2, x_3);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = l_Lean_Parser_identFn___closed__1;
x_10 = l_Lean_Parser_ParserState_mkErrorAt(x_5, x_9, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 3)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_name_eq(x_13, x_1);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep(x_15, x_1);
x_17 = l_Lean_Parser_identEqFn___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Char_quote___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_Parser_ParserState_mkErrorAt(x_5, x_20, x_4);
return x_21;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
lean_dec(x_1);
x_22 = l_Lean_Parser_identFn___closed__1;
x_23 = l_Lean_Parser_ParserState_mkErrorAt(x_5, x_22, x_4);
return x_23;
}
}
}
}
lean_object* l_Lean_Parser_identEq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_identEqFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_identNoAntiquot___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_instCoeStringParser(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_String_trim(x_1);
lean_inc(x_2);
x_3 = l_Lean_Parser_symbolInfo(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_instCoeStringParser___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instCoeStringParser(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_ParserState_keepNewError_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_ParserState_keepNewError_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_ParserState_keepNewError_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_ParserState_keepNewError(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Array_shrink___rarg(x_4, x_2);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_10 = l_Array_shrink___rarg(x_6, x_2);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Parser_ParserState_keepNewError___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_keepNewError(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_ParserState_keepPrevError_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_ParserState_keepPrevError_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_ParserState_keepPrevError_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_ParserState_keepPrevError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 3);
lean_dec(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_dec(x_8);
x_9 = l_Array_shrink___rarg(x_6, x_2);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_Array_shrink___rarg(x_10, x_2);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_4);
return x_13;
}
}
}
lean_object* l_Lean_Parser_ParserState_keepPrevError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_ParserState_keepPrevError(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Parser_ParserState_mergeErrors_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_apply_1(x_3, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_apply_4(x_2, x_6, x_7, x_8, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Parser_ParserState_mergeErrors_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_ParserState_mergeErrors_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_ParserState_mergeErrors(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = l_Lean_Parser_Error_beq(x_3, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
x_16 = l_Array_shrink___rarg(x_5, x_2);
x_17 = l_Lean_Parser_Error_merge(x_3, x_9);
lean_ctor_set(x_4, 0, x_17);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_18 = l_Array_shrink___rarg(x_5, x_2);
x_19 = l_Lean_Parser_Error_merge(x_3, x_9);
lean_ctor_set(x_4, 0, x_19);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_6);
lean_ctor_set(x_20, 2, x_7);
lean_ctor_set(x_20, 3, x_4);
return x_20;
}
}
else
{
lean_free_object(x_4);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_1;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
x_22 = l_Lean_Parser_Error_beq(x_3, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_23 = x_1;
} else {
 lean_dec_ref(x_1);
 x_23 = lean_box(0);
}
x_24 = l_Array_shrink___rarg(x_5, x_2);
x_25 = l_Lean_Parser_Error_merge(x_3, x_21);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
if (lean_is_scalar(x_23)) {
 x_27 = lean_alloc_ctor(0, 4, 0);
} else {
 x_27 = x_23;
}
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_6);
lean_ctor_set(x_27, 2, x_7);
lean_ctor_set(x_27, 3, x_26);
return x_27;
}
else
{
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_1;
}
}
}
}
}
lean_object* l_Lean_Parser_ParserState_mergeErrors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_mergeErrors(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_ParserState_keepLatest_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Parser_ParserState_keepLatest_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_ParserState_keepLatest_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_ParserState_keepLatest(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 3);
lean_dec(x_5);
x_6 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_4);
x_7 = l_Array_shrink___rarg(x_4, x_2);
x_8 = lean_array_push(x_7, x_6);
x_9 = lean_box(0);
lean_ctor_set(x_1, 3, x_9);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_13 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_10);
x_14 = l_Array_shrink___rarg(x_10, x_2);
x_15 = lean_array_push(x_14, x_13);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_16);
return x_17;
}
}
}
lean_object* l_Lean_Parser_ParserState_keepLatest___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_keepLatest(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_ParserState_replaceLongest(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_keepLatest(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_ParserState_replaceLongest___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_replaceLongest(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_invalidLongestMatchParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("longestMatch parsers must generate exactly one Syntax node");
return x_1;
}
}
lean_object* l_Lean_Parser_invalidLongestMatchParser(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_invalidLongestMatchParser___closed__1;
x_3 = l_Lean_Parser_ParserState_mkError(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_runLongestMatchParser_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_runLongestMatchParser_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_runLongestMatchParser_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_runLongestMatchParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_apply_2(x_2, x_3, x_4);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_6, x_13);
lean_dec(x_6);
x_15 = lean_nat_dec_eq(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Parser_invalidLongestMatchParser___closed__1;
x_17 = l_Lean_Parser_ParserState_mkError(x_7, x_16);
return x_17;
}
else
{
return x_7;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_Lean_Parser_ParserState_pushSyntax(x_4, x_18);
x_20 = lean_apply_2(x_2, x_3, x_19);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
x_22 = lean_box(0);
x_23 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_dec(x_6);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
x_25 = lean_array_get_size(x_24);
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_nat_add(x_6, x_26);
x_28 = lean_nat_dec_eq(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_24);
lean_dec(x_6);
x_29 = l_Lean_Parser_invalidLongestMatchParser___closed__1;
x_30 = l_Lean_Parser_ParserState_mkError(x_20, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_24);
lean_dec(x_24);
x_32 = l_Lean_Parser_ParserState_shrinkStack(x_20, x_6);
lean_dec(x_6);
x_33 = l_Lean_Parser_ParserState_pushSyntax(x_32, x_31);
return x_33;
}
}
}
}
}
lean_object* l_Lean_Parser_longestMatchStep_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_6, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_apply_2(x_5, x_13, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_Parser_longestMatchStep_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_longestMatchStep_match__1___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_longestMatchStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
x_13 = l_Lean_Parser_ParserState_restore(x_8, x_12, x_3);
x_14 = l_Lean_Parser_runLongestMatchParser(x_1, x_6, x_7, x_13);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_28; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_28 = lean_nat_dec_lt(x_10, x_16);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = lean_nat_dec_eq(x_16, x_10);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_box(0);
x_17 = x_30;
goto block_27;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_lt(x_4, x_5);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_box(0);
x_17 = x_32;
goto block_27;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
x_33 = l_Lean_Parser_ParserState_keepLatest(x_14, x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_5);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
x_35 = l_Lean_Parser_ParserState_keepLatest(x_14, x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_5);
return x_36;
}
block_27:
{
uint8_t x_18; 
lean_dec(x_17);
x_18 = lean_nat_dec_lt(x_16, x_10);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = lean_nat_dec_eq(x_16, x_10);
lean_dec(x_16);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_5);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_lt(x_5, x_4);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_23 = l_Lean_Parser_ParserState_restore(x_14, x_12, x_10);
lean_dec(x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_16);
lean_dec(x_5);
x_25 = l_Lean_Parser_ParserState_restore(x_14, x_12, x_10);
lean_dec(x_12);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_4);
return x_26;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_15);
lean_dec(x_5);
x_37 = l_Lean_Parser_ParserState_restore(x_14, x_12, x_10);
lean_dec(x_12);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_4);
return x_38;
}
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_14, 3);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_40 = lean_ctor_get(x_14, 0);
lean_inc(x_40);
x_41 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_40);
lean_dec(x_40);
x_42 = l_Lean_Parser_ParserState_shrinkStack(x_14, x_2);
x_43 = l_Lean_Parser_ParserState_pushSyntax(x_42, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_5);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_60; 
lean_dec(x_39);
x_45 = lean_ctor_get(x_9, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
x_60 = lean_nat_dec_lt(x_10, x_46);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = lean_nat_dec_eq(x_46, x_10);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_box(0);
x_47 = x_62;
goto block_59;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_lt(x_4, x_5);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_box(0);
x_47 = x_64;
goto block_59;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_65 = l_Lean_Parser_ParserState_keepNewError(x_14, x_12);
lean_dec(x_12);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_5);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_67 = l_Lean_Parser_ParserState_keepNewError(x_14, x_12);
lean_dec(x_12);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_5);
return x_68;
}
block_59:
{
uint8_t x_48; 
lean_dec(x_47);
x_48 = lean_nat_dec_lt(x_46, x_10);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = lean_nat_dec_eq(x_46, x_10);
lean_dec(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_50 = l_Lean_Parser_ParserState_mergeErrors(x_14, x_12, x_45);
lean_dec(x_12);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_5);
return x_51;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_lt(x_5, x_4);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_53 = l_Lean_Parser_ParserState_mergeErrors(x_14, x_12, x_45);
lean_dec(x_12);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_5);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_45);
lean_dec(x_5);
x_55 = l_Lean_Parser_ParserState_keepPrevError(x_14, x_12, x_10, x_9);
lean_dec(x_12);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_4);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_5);
x_57 = l_Lean_Parser_ParserState_keepPrevError(x_14, x_12, x_10, x_9);
lean_dec(x_12);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_4);
return x_58;
}
}
}
}
}
}
lean_object* l_Lean_Parser_longestMatchStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_longestMatchStep(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Parser_longestMatchMkResult(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
x_4 = lean_box(0);
x_5 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_1, x_6);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_nat_dec_lt(x_7, x_9);
lean_dec(x_9);
lean_dec(x_7);
if (x_10 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_choiceKind;
x_12 = l_Lean_Parser_ParserState_mkNode(x_2, x_11, x_1);
return x_12;
}
}
}
}
lean_object* l_Lean_Parser_longestMatchFnAux_parse_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Parser_longestMatchFnAux_parse_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_longestMatchFnAux_parse_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_longestMatchFnAux_parse_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_longestMatchFnAux_parse_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_longestMatchFnAux_parse_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_longestMatchFnAux_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = l_Lean_Parser_longestMatchMkResult(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_1);
x_14 = l_Lean_Parser_longestMatchStep(x_1, x_2, x_3, x_4, x_11, x_13, x_6, x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_4 = x_16;
x_5 = x_10;
x_7 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_Parser_longestMatchFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_longestMatchFnAux_parse(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Parser_longestMatchFn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_2(x_4, x_10, x_7);
return x_11;
}
}
}
}
lean_object* l_Lean_Parser_longestMatchFn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_longestMatchFn_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_longestMatchFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("longestMatch: empty list");
return x_1;
}
}
lean_object* l_Lean_Parser_longestMatchFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = l_Lean_Parser_longestMatchFn___closed__1;
x_6 = l_Lean_Parser_ParserState_mkError(x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Parser_runLongestMatchParser(x_1, x_10, x_3, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_3);
lean_inc(x_1);
x_18 = l_Lean_Parser_runLongestMatchParser(x_1, x_17, x_3, x_4);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
x_20 = lean_box(0);
x_21 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_Parser_ParserState_shrinkStack(x_18, x_14);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_dec(x_12);
x_24 = l_Lean_Parser_longestMatchFnAux_parse(x_1, x_14, x_15, x_23, x_7, x_3, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_dec(x_12);
x_26 = l_Lean_Parser_longestMatchFnAux_parse(x_1, x_14, x_15, x_25, x_7, x_3, x_18);
return x_26;
}
}
}
}
}
lean_object* l_Lean_Parser_anyOfFn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
lean_dec(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_4, x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_3(x_5, x_9, x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_4(x_6, x_11, x_8, x_2, x_3);
return x_12;
}
}
}
}
lean_object* l_Lean_Parser_anyOfFn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_anyOfFn_match__1___rarg), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_anyOfFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("anyOf: empty list");
return x_1;
}
}
lean_object* l_Lean_Parser_anyOfFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = l_Lean_Parser_anyOfFn___closed__1;
x_5 = l_Lean_Parser_ParserState_mkError(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, x_2, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_anyOfFn), 3, 1);
lean_closure_set(x_12, 0, x_6);
x_13 = 1;
x_14 = l_Lean_Parser_orelseFnCore(x_11, x_12, x_13, x_2, x_3);
return x_14;
}
}
}
}
lean_object* l_Lean_Parser_checkColGeFn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_checkColGeFn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkColGeFn_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_checkColGeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 4);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_FileMap_toPosition(x_7, x_5);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = l_Lean_FileMap_toPosition(x_7, x_9);
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_nat_dec_le(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_14;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
}
lean_object* l_Lean_Parser_checkColGe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkColGeFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_errorAtSavedPos___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_checkColGtFn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_checkColGtFn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkColGtFn_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_checkColGtFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 4);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_FileMap_toPosition(x_7, x_5);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = l_Lean_FileMap_toPosition(x_7, x_9);
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_nat_dec_lt(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_14;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
}
lean_object* l_Lean_Parser_checkColGt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkColGtFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_errorAtSavedPos___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_checkLineEqFn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_checkLineEqFn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkLineEqFn_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_checkLineEqFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 4);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_FileMap_toPosition(x_7, x_5);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = l_Lean_FileMap_toPosition(x_7, x_9);
lean_dec(x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_14;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
}
lean_object* l_Lean_Parser_checkLineEq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkLineEqFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_errorAtSavedPos___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_withPosition___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 4);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_2, 4, x_13);
x_14 = lean_apply_2(x_5, x_2, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_7, 2);
x_18 = lean_ctor_get(x_7, 3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_18);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_2, 4, x_21);
lean_ctor_set(x_2, 1, x_19);
x_22 = lean_apply_2(x_5, x_2, x_3);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
x_25 = lean_ctor_get(x_4, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_ctor_get(x_7, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_7, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_7, 3);
lean_inc(x_30);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 x_31 = x_7;
} else {
 lean_dec_ref(x_7);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 4, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_29);
lean_ctor_set(x_32, 3, x_30);
x_33 = lean_ctor_get(x_3, 1);
lean_inc(x_33);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_2, 4, x_34);
lean_ctor_set(x_2, 1, x_32);
lean_ctor_set(x_2, 0, x_26);
x_35 = lean_apply_2(x_5, x_2, x_3);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_36 = lean_ctor_get(x_2, 1);
x_37 = lean_ctor_get(x_2, 2);
x_38 = lean_ctor_get(x_2, 3);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
x_41 = lean_ctor_get(x_2, 5);
lean_inc(x_41);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_2);
x_42 = lean_ctor_get(x_4, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_4, 2);
lean_inc(x_44);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 x_45 = x_4;
} else {
 lean_dec_ref(x_4);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 3, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_44);
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_36, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_36, 3);
lean_inc(x_50);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 x_51 = x_36;
} else {
 lean_dec_ref(x_36);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 4, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 2, x_49);
lean_ctor_set(x_52, 3, x_50);
x_53 = lean_ctor_get(x_3, 1);
lean_inc(x_53);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_37);
lean_ctor_set(x_55, 3, x_38);
lean_ctor_set(x_55, 4, x_54);
lean_ctor_set(x_55, 5, x_41);
lean_ctor_set_uint8(x_55, sizeof(void*)*6, x_39);
lean_ctor_set_uint8(x_55, sizeof(void*)*6 + 1, x_40);
x_56 = lean_apply_2(x_5, x_55, x_3);
return x_56;
}
}
}
lean_object* l_Lean_Parser_withPosition(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lambda__1), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_3);
return x_1;
}
else
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
lean_object* l_Lean_Parser_withoutPosition___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 4);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
lean_ctor_set(x_2, 4, x_12);
x_13 = lean_apply_2(x_5, x_2, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_17);
x_19 = lean_box(0);
lean_ctor_set(x_2, 4, x_19);
lean_ctor_set(x_2, 1, x_18);
x_20 = lean_apply_2(x_5, x_2, x_3);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get(x_4, 2);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 3);
lean_inc(x_28);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 x_29 = x_7;
} else {
 lean_dec_ref(x_7);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 4, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_28);
x_31 = lean_box(0);
lean_ctor_set(x_2, 4, x_31);
lean_ctor_set(x_2, 1, x_30);
lean_ctor_set(x_2, 0, x_24);
x_32 = lean_apply_2(x_5, x_2, x_3);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_33 = lean_ctor_get(x_2, 1);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_ctor_get(x_2, 3);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
x_38 = lean_ctor_get(x_2, 5);
lean_inc(x_38);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_2);
x_39 = lean_ctor_get(x_4, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 2);
lean_inc(x_41);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 x_42 = x_4;
} else {
 lean_dec_ref(x_4);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 3, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_41);
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_33, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_33, 3);
lean_inc(x_47);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 lean_ctor_release(x_33, 3);
 x_48 = x_33;
} else {
 lean_dec_ref(x_33);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 4, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_47);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_34);
lean_ctor_set(x_51, 3, x_35);
lean_ctor_set(x_51, 4, x_50);
lean_ctor_set(x_51, 5, x_38);
lean_ctor_set_uint8(x_51, sizeof(void*)*6, x_36);
lean_ctor_set_uint8(x_51, sizeof(void*)*6 + 1, x_37);
x_52 = lean_apply_2(x_5, x_51, x_3);
return x_52;
}
}
}
lean_object* l_Lean_Parser_withoutPosition(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition___lambda__1), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_3);
return x_1;
}
else
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
lean_object* l_Lean_Parser_withForbidden___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_3, 5);
lean_dec(x_9);
x_10 = lean_ctor_get(x_3, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_3, 5, x_13);
x_14 = lean_apply_2(x_6, x_3, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_3, 5, x_20);
lean_ctor_set(x_3, 1, x_19);
x_21 = lean_apply_2(x_6, x_3, x_4);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
x_24 = lean_ctor_get(x_5, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_ctor_get(x_8, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_8, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_8, 3);
lean_inc(x_29);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_30 = x_8;
} else {
 lean_dec_ref(x_8);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 4, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_29);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_3, 5, x_32);
lean_ctor_set(x_3, 1, x_31);
lean_ctor_set(x_3, 0, x_25);
x_33 = lean_apply_2(x_6, x_3, x_4);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_34 = lean_ctor_get(x_3, 1);
x_35 = lean_ctor_get(x_3, 2);
x_36 = lean_ctor_get(x_3, 3);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_38 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_39 = lean_ctor_get(x_3, 4);
lean_inc(x_39);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_3);
x_40 = lean_ctor_get(x_5, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_5, 2);
lean_inc(x_42);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_43 = x_5;
} else {
 lean_dec_ref(x_5);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 3, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_41);
lean_ctor_set(x_44, 2, x_42);
x_45 = lean_ctor_get(x_34, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_34, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_34, 3);
lean_inc(x_48);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 lean_ctor_release(x_34, 3);
 x_49 = x_34;
} else {
 lean_dec_ref(x_34);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 4, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_50, 2, x_47);
lean_ctor_set(x_50, 3, x_48);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_2);
x_52 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_52, 2, x_35);
lean_ctor_set(x_52, 3, x_36);
lean_ctor_set(x_52, 4, x_39);
lean_ctor_set(x_52, 5, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*6, x_37);
lean_ctor_set_uint8(x_52, sizeof(void*)*6 + 1, x_38);
x_53 = lean_apply_2(x_6, x_52, x_4);
return x_53;
}
}
}
lean_object* l_Lean_Parser_withForbidden(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_withForbidden___lambda__1), 4, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 1);
lean_dec(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_dec(x_7);
lean_ctor_set(x_2, 1, x_4);
return x_2;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
}
lean_object* l_Lean_Parser_withoutForbidden___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 5);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
lean_ctor_set(x_2, 5, x_12);
x_13 = lean_apply_2(x_5, x_2, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_17);
x_19 = lean_box(0);
lean_ctor_set(x_2, 5, x_19);
lean_ctor_set(x_2, 1, x_18);
x_20 = lean_apply_2(x_5, x_2, x_3);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get(x_4, 2);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 3);
lean_inc(x_28);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 x_29 = x_7;
} else {
 lean_dec_ref(x_7);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 4, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_28);
x_31 = lean_box(0);
lean_ctor_set(x_2, 5, x_31);
lean_ctor_set(x_2, 1, x_30);
lean_ctor_set(x_2, 0, x_24);
x_32 = lean_apply_2(x_5, x_2, x_3);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_33 = lean_ctor_get(x_2, 1);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_ctor_get(x_2, 3);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
x_38 = lean_ctor_get(x_2, 4);
lean_inc(x_38);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_2);
x_39 = lean_ctor_get(x_4, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 2);
lean_inc(x_41);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 x_42 = x_4;
} else {
 lean_dec_ref(x_4);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 3, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_41);
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_33, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_33, 3);
lean_inc(x_47);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 lean_ctor_release(x_33, 3);
 x_48 = x_33;
} else {
 lean_dec_ref(x_33);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 4, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_47);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_34);
lean_ctor_set(x_51, 3, x_35);
lean_ctor_set(x_51, 4, x_38);
lean_ctor_set(x_51, 5, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*6, x_36);
lean_ctor_set_uint8(x_51, sizeof(void*)*6 + 1, x_37);
x_52 = lean_apply_2(x_5, x_51, x_3);
return x_52;
}
}
}
lean_object* l_Lean_Parser_withoutForbidden(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_withoutForbidden___lambda__1), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_3);
return x_1;
}
else
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Parser_eoiFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected end of file");
return x_1;
}
}
lean_object* l_Lean_Parser_eoiFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_string_utf8_at_end(x_5, x_3);
lean_dec(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Parser_eoiFn___closed__1;
x_8 = l_Lean_Parser_ParserState_mkError(x_2, x_7);
return x_8;
}
else
{
return x_2;
}
}
}
lean_object* l_Lean_Parser_eoiFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_eoiFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_eoi___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_eoiFn___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_eoi___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_errorAtSavedPos___closed__1;
x_2 = l_Lean_Parser_eoi___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_eoi() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_eoi___closed__2;
return x_1;
}
}
lean_object* l_Lean_Parser_TokenMap_insert_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_TokenMap_insert_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_insert_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
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
lean_object* l_Std_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = l_Lean_Name_quickLt(x_2, x_10);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Name_quickLt(x_10, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_10);
x_15 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_12, x_2, x_3);
x_17 = 0;
lean_ctor_set(x_1, 3, x_16);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_17);
return x_1;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_9, x_2, x_3);
x_19 = 0;
lean_ctor_set(x_1, 0, x_18);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = l_Lean_Name_quickLt(x_2, x_21);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Name_quickLt(x_21, x_2);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_21);
x_26 = 0;
x_27 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set(x_27, 2, x_3);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_26);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_23, x_2, x_3);
x_29 = 0;
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_22);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_29);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_20, x_2, x_3);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = l_Lean_Name_quickLt(x_2, x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Name_quickLt(x_36, x_2);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_37);
lean_dec(x_36);
x_41 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_41);
return x_1;
}
else
{
uint8_t x_42; 
x_42 = l_Std_RBNode_isRed___rarg(x_38);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_38, x_2, x_3);
x_44 = 1;
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_44);
return x_1;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_38, x_2, x_3);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 3);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_45, 3);
lean_dec(x_49);
x_50 = lean_ctor_get(x_45, 0);
lean_dec(x_50);
x_51 = 0;
lean_ctor_set(x_45, 0, x_47);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_51);
x_52 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_52);
return x_1;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_45, 1);
x_54 = lean_ctor_get(x_45, 2);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_45);
x_55 = 0;
x_56 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_56, 2, x_54);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_55);
x_57 = 1;
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_57);
return x_1;
}
}
else
{
uint8_t x_58; 
x_58 = lean_ctor_get_uint8(x_47, sizeof(void*)*4);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_45);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_45, 1);
x_61 = lean_ctor_get(x_45, 2);
x_62 = lean_ctor_get(x_45, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_45, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_47);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_47, 0);
x_66 = lean_ctor_get(x_47, 1);
x_67 = lean_ctor_get(x_47, 2);
x_68 = lean_ctor_get(x_47, 3);
x_69 = 1;
lean_ctor_set(x_47, 3, x_46);
lean_ctor_set(x_47, 2, x_37);
lean_ctor_set(x_47, 1, x_36);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_69);
lean_ctor_set(x_45, 3, x_68);
lean_ctor_set(x_45, 2, x_67);
lean_ctor_set(x_45, 1, x_66);
lean_ctor_set(x_45, 0, x_65);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_69);
x_70 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_61);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_1, 0, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_70);
return x_1;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; 
x_71 = lean_ctor_get(x_47, 0);
x_72 = lean_ctor_get(x_47, 1);
x_73 = lean_ctor_get(x_47, 2);
x_74 = lean_ctor_get(x_47, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_47);
x_75 = 1;
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_35);
lean_ctor_set(x_76, 1, x_36);
lean_ctor_set(x_76, 2, x_37);
lean_ctor_set(x_76, 3, x_46);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_75);
lean_ctor_set(x_45, 3, x_74);
lean_ctor_set(x_45, 2, x_73);
lean_ctor_set(x_45, 1, x_72);
lean_ctor_set(x_45, 0, x_71);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_75);
x_77 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_61);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_1, 0, x_76);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_77);
return x_1;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_78 = lean_ctor_get(x_45, 1);
x_79 = lean_ctor_get(x_45, 2);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_45);
x_80 = lean_ctor_get(x_47, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_47, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_47, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_47, 3);
lean_inc(x_83);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_84 = x_47;
} else {
 lean_dec_ref(x_47);
 x_84 = lean_box(0);
}
x_85 = 1;
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(1, 4, 1);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_35);
lean_ctor_set(x_86, 1, x_36);
lean_ctor_set(x_86, 2, x_37);
lean_ctor_set(x_86, 3, x_46);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_85);
x_87 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_81);
lean_ctor_set(x_87, 2, x_82);
lean_ctor_set(x_87, 3, x_83);
lean_ctor_set_uint8(x_87, sizeof(void*)*4, x_85);
x_88 = 0;
lean_ctor_set(x_1, 3, x_87);
lean_ctor_set(x_1, 2, x_79);
lean_ctor_set(x_1, 1, x_78);
lean_ctor_set(x_1, 0, x_86);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_88);
return x_1;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_45);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_45, 3);
lean_dec(x_90);
x_91 = lean_ctor_get(x_45, 0);
lean_dec(x_91);
x_92 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_92);
x_93 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_93);
return x_1;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_45, 1);
x_95 = lean_ctor_get(x_45, 2);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_45);
x_96 = 0;
x_97 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_97, 0, x_46);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_47);
lean_ctor_set_uint8(x_97, sizeof(void*)*4, x_96);
x_98 = 1;
lean_ctor_set(x_1, 3, x_97);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_98);
return x_1;
}
}
}
}
else
{
uint8_t x_99; 
x_99 = lean_ctor_get_uint8(x_46, sizeof(void*)*4);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_45);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_45, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_46);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; 
x_103 = lean_ctor_get(x_46, 0);
x_104 = lean_ctor_get(x_46, 1);
x_105 = lean_ctor_get(x_46, 2);
x_106 = lean_ctor_get(x_46, 3);
x_107 = 1;
lean_ctor_set(x_46, 3, x_103);
lean_ctor_set(x_46, 2, x_37);
lean_ctor_set(x_46, 1, x_36);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_107);
lean_ctor_set(x_45, 0, x_106);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_107);
x_108 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_105);
lean_ctor_set(x_1, 1, x_104);
lean_ctor_set(x_1, 0, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_108);
return x_1;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; uint8_t x_115; 
x_109 = lean_ctor_get(x_46, 0);
x_110 = lean_ctor_get(x_46, 1);
x_111 = lean_ctor_get(x_46, 2);
x_112 = lean_ctor_get(x_46, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_46);
x_113 = 1;
x_114 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_114, 0, x_35);
lean_ctor_set(x_114, 1, x_36);
lean_ctor_set(x_114, 2, x_37);
lean_ctor_set(x_114, 3, x_109);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_113);
lean_ctor_set(x_45, 0, x_112);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_113);
x_115 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_111);
lean_ctor_set(x_1, 1, x_110);
lean_ctor_set(x_1, 0, x_114);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_115);
return x_1;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_116 = lean_ctor_get(x_45, 1);
x_117 = lean_ctor_get(x_45, 2);
x_118 = lean_ctor_get(x_45, 3);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_45);
x_119 = lean_ctor_get(x_46, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_46, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_46, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_46, 3);
lean_inc(x_122);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_123 = x_46;
} else {
 lean_dec_ref(x_46);
 x_123 = lean_box(0);
}
x_124 = 1;
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(1, 4, 1);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_35);
lean_ctor_set(x_125, 1, x_36);
lean_ctor_set(x_125, 2, x_37);
lean_ctor_set(x_125, 3, x_119);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_124);
x_126 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_116);
lean_ctor_set(x_126, 2, x_117);
lean_ctor_set(x_126, 3, x_118);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_124);
x_127 = 0;
lean_ctor_set(x_1, 3, x_126);
lean_ctor_set(x_1, 2, x_121);
lean_ctor_set(x_1, 1, x_120);
lean_ctor_set(x_1, 0, x_125);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_127);
return x_1;
}
}
else
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_45, 3);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_45);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_45, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_45, 0);
lean_dec(x_131);
x_132 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_132);
x_133 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_133);
return x_1;
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; uint8_t x_138; 
x_134 = lean_ctor_get(x_45, 1);
x_135 = lean_ctor_get(x_45, 2);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_45);
x_136 = 0;
x_137 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_137, 0, x_46);
lean_ctor_set(x_137, 1, x_134);
lean_ctor_set(x_137, 2, x_135);
lean_ctor_set(x_137, 3, x_128);
lean_ctor_set_uint8(x_137, sizeof(void*)*4, x_136);
x_138 = 1;
lean_ctor_set(x_1, 3, x_137);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_138);
return x_1;
}
}
else
{
uint8_t x_139; 
x_139 = lean_ctor_get_uint8(x_128, sizeof(void*)*4);
if (x_139 == 0)
{
uint8_t x_140; 
lean_free_object(x_1);
x_140 = !lean_is_exclusive(x_45);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_45, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_45, 0);
lean_dec(x_142);
x_143 = !lean_is_exclusive(x_128);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; 
x_144 = lean_ctor_get(x_128, 0);
x_145 = lean_ctor_get(x_128, 1);
x_146 = lean_ctor_get(x_128, 2);
x_147 = lean_ctor_get(x_128, 3);
x_148 = 1;
lean_inc(x_46);
lean_ctor_set(x_128, 3, x_46);
lean_ctor_set(x_128, 2, x_37);
lean_ctor_set(x_128, 1, x_36);
lean_ctor_set(x_128, 0, x_35);
x_149 = !lean_is_exclusive(x_46);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_150 = lean_ctor_get(x_46, 3);
lean_dec(x_150);
x_151 = lean_ctor_get(x_46, 2);
lean_dec(x_151);
x_152 = lean_ctor_get(x_46, 1);
lean_dec(x_152);
x_153 = lean_ctor_get(x_46, 0);
lean_dec(x_153);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_148);
lean_ctor_set(x_46, 3, x_147);
lean_ctor_set(x_46, 2, x_146);
lean_ctor_set(x_46, 1, x_145);
lean_ctor_set(x_46, 0, x_144);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_148);
x_154 = 0;
lean_ctor_set(x_45, 3, x_46);
lean_ctor_set(x_45, 0, x_128);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_154);
return x_45;
}
else
{
lean_object* x_155; uint8_t x_156; 
lean_dec(x_46);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_148);
x_155 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_155, 0, x_144);
lean_ctor_set(x_155, 1, x_145);
lean_ctor_set(x_155, 2, x_146);
lean_ctor_set(x_155, 3, x_147);
lean_ctor_set_uint8(x_155, sizeof(void*)*4, x_148);
x_156 = 0;
lean_ctor_set(x_45, 3, x_155);
lean_ctor_set(x_45, 0, x_128);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_156);
return x_45;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_157 = lean_ctor_get(x_128, 0);
x_158 = lean_ctor_get(x_128, 1);
x_159 = lean_ctor_get(x_128, 2);
x_160 = lean_ctor_get(x_128, 3);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_128);
x_161 = 1;
lean_inc(x_46);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_35);
lean_ctor_set(x_162, 1, x_36);
lean_ctor_set(x_162, 2, x_37);
lean_ctor_set(x_162, 3, x_46);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_163 = x_46;
} else {
 lean_dec_ref(x_46);
 x_163 = lean_box(0);
}
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_161);
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 4, 1);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_157);
lean_ctor_set(x_164, 1, x_158);
lean_ctor_set(x_164, 2, x_159);
lean_ctor_set(x_164, 3, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_161);
x_165 = 0;
lean_ctor_set(x_45, 3, x_164);
lean_ctor_set(x_45, 0, x_162);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_165);
return x_45;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; 
x_166 = lean_ctor_get(x_45, 1);
x_167 = lean_ctor_get(x_45, 2);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_45);
x_168 = lean_ctor_get(x_128, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_128, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_128, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_128, 3);
lean_inc(x_171);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 x_172 = x_128;
} else {
 lean_dec_ref(x_128);
 x_172 = lean_box(0);
}
x_173 = 1;
lean_inc(x_46);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(1, 4, 1);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_35);
lean_ctor_set(x_174, 1, x_36);
lean_ctor_set(x_174, 2, x_37);
lean_ctor_set(x_174, 3, x_46);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_175 = x_46;
} else {
 lean_dec_ref(x_46);
 x_175 = lean_box(0);
}
lean_ctor_set_uint8(x_174, sizeof(void*)*4, x_173);
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 4, 1);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_168);
lean_ctor_set(x_176, 1, x_169);
lean_ctor_set(x_176, 2, x_170);
lean_ctor_set(x_176, 3, x_171);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_173);
x_177 = 0;
x_178 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_166);
lean_ctor_set(x_178, 2, x_167);
lean_ctor_set(x_178, 3, x_176);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_177);
return x_178;
}
}
else
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_45);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_45, 3);
lean_dec(x_180);
x_181 = lean_ctor_get(x_45, 0);
lean_dec(x_181);
x_182 = !lean_is_exclusive(x_46);
if (x_182 == 0)
{
uint8_t x_183; uint8_t x_184; 
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_139);
x_183 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_183);
x_184 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_184);
return x_1;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_191; 
x_185 = lean_ctor_get(x_46, 0);
x_186 = lean_ctor_get(x_46, 1);
x_187 = lean_ctor_get(x_46, 2);
x_188 = lean_ctor_get(x_46, 3);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_46);
x_189 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_189, 0, x_185);
lean_ctor_set(x_189, 1, x_186);
lean_ctor_set(x_189, 2, x_187);
lean_ctor_set(x_189, 3, x_188);
lean_ctor_set_uint8(x_189, sizeof(void*)*4, x_139);
x_190 = 0;
lean_ctor_set(x_45, 0, x_189);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_190);
x_191 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_191);
return x_1;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; uint8_t x_202; 
x_192 = lean_ctor_get(x_45, 1);
x_193 = lean_ctor_get(x_45, 2);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_45);
x_194 = lean_ctor_get(x_46, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_46, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_46, 2);
lean_inc(x_196);
x_197 = lean_ctor_get(x_46, 3);
lean_inc(x_197);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_198 = x_46;
} else {
 lean_dec_ref(x_46);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 4, 1);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_194);
lean_ctor_set(x_199, 1, x_195);
lean_ctor_set(x_199, 2, x_196);
lean_ctor_set(x_199, 3, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_139);
x_200 = 0;
x_201 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_192);
lean_ctor_set(x_201, 2, x_193);
lean_ctor_set(x_201, 3, x_128);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_200);
x_202 = 1;
lean_ctor_set(x_1, 3, x_201);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
}
}
}
}
}
}
}
}
else
{
uint8_t x_203; 
x_203 = l_Std_RBNode_isRed___rarg(x_35);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_35, x_2, x_3);
x_205 = 1;
lean_ctor_set(x_1, 0, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_205);
return x_1;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_35, x_2, x_3);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_206, 3);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_206);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; uint8_t x_213; 
x_210 = lean_ctor_get(x_206, 3);
lean_dec(x_210);
x_211 = lean_ctor_get(x_206, 0);
lean_dec(x_211);
x_212 = 0;
lean_ctor_set(x_206, 0, x_208);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_212);
x_213 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_213);
return x_1;
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_206, 1);
x_215 = lean_ctor_get(x_206, 2);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_206);
x_216 = 0;
x_217 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_217, 0, x_208);
lean_ctor_set(x_217, 1, x_214);
lean_ctor_set(x_217, 2, x_215);
lean_ctor_set(x_217, 3, x_208);
lean_ctor_set_uint8(x_217, sizeof(void*)*4, x_216);
x_218 = 1;
lean_ctor_set(x_1, 0, x_217);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_218);
return x_1;
}
}
else
{
uint8_t x_219; 
x_219 = lean_ctor_get_uint8(x_208, sizeof(void*)*4);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_206);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_221 = lean_ctor_get(x_206, 1);
x_222 = lean_ctor_get(x_206, 2);
x_223 = lean_ctor_get(x_206, 3);
lean_dec(x_223);
x_224 = lean_ctor_get(x_206, 0);
lean_dec(x_224);
x_225 = !lean_is_exclusive(x_208);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_231; 
x_226 = lean_ctor_get(x_208, 0);
x_227 = lean_ctor_get(x_208, 1);
x_228 = lean_ctor_get(x_208, 2);
x_229 = lean_ctor_get(x_208, 3);
x_230 = 1;
lean_ctor_set(x_208, 3, x_226);
lean_ctor_set(x_208, 2, x_222);
lean_ctor_set(x_208, 1, x_221);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_230);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_229);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_230);
x_231 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_208);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_231);
return x_1;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; uint8_t x_238; 
x_232 = lean_ctor_get(x_208, 0);
x_233 = lean_ctor_get(x_208, 1);
x_234 = lean_ctor_get(x_208, 2);
x_235 = lean_ctor_get(x_208, 3);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_208);
x_236 = 1;
x_237 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_237, 0, x_207);
lean_ctor_set(x_237, 1, x_221);
lean_ctor_set(x_237, 2, x_222);
lean_ctor_set(x_237, 3, x_232);
lean_ctor_set_uint8(x_237, sizeof(void*)*4, x_236);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_235);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_236);
x_238 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_234);
lean_ctor_set(x_1, 1, x_233);
lean_ctor_set(x_1, 0, x_237);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_238);
return x_1;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_239 = lean_ctor_get(x_206, 1);
x_240 = lean_ctor_get(x_206, 2);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_206);
x_241 = lean_ctor_get(x_208, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_208, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_208, 2);
lean_inc(x_243);
x_244 = lean_ctor_get(x_208, 3);
lean_inc(x_244);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 lean_ctor_release(x_208, 3);
 x_245 = x_208;
} else {
 lean_dec_ref(x_208);
 x_245 = lean_box(0);
}
x_246 = 1;
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(1, 4, 1);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_207);
lean_ctor_set(x_247, 1, x_239);
lean_ctor_set(x_247, 2, x_240);
lean_ctor_set(x_247, 3, x_241);
lean_ctor_set_uint8(x_247, sizeof(void*)*4, x_246);
x_248 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_248, 0, x_244);
lean_ctor_set(x_248, 1, x_36);
lean_ctor_set(x_248, 2, x_37);
lean_ctor_set(x_248, 3, x_38);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_246);
x_249 = 0;
lean_ctor_set(x_1, 3, x_248);
lean_ctor_set(x_1, 2, x_243);
lean_ctor_set(x_1, 1, x_242);
lean_ctor_set(x_1, 0, x_247);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_249);
return x_1;
}
}
else
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_206);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_254; 
x_251 = lean_ctor_get(x_206, 3);
lean_dec(x_251);
x_252 = lean_ctor_get(x_206, 0);
lean_dec(x_252);
x_253 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_253);
x_254 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_254);
return x_1;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_255 = lean_ctor_get(x_206, 1);
x_256 = lean_ctor_get(x_206, 2);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_206);
x_257 = 0;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_207);
lean_ctor_set(x_258, 1, x_255);
lean_ctor_set(x_258, 2, x_256);
lean_ctor_set(x_258, 3, x_208);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
x_259 = 1;
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
else
{
uint8_t x_260; 
x_260 = lean_ctor_get_uint8(x_207, sizeof(void*)*4);
if (x_260 == 0)
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_206);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_262 = lean_ctor_get(x_206, 1);
x_263 = lean_ctor_get(x_206, 2);
x_264 = lean_ctor_get(x_206, 3);
x_265 = lean_ctor_get(x_206, 0);
lean_dec(x_265);
x_266 = !lean_is_exclusive(x_207);
if (x_266 == 0)
{
uint8_t x_267; uint8_t x_268; 
x_267 = 1;
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_267);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_267);
x_268 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_207);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_268);
return x_1;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; uint8_t x_275; 
x_269 = lean_ctor_get(x_207, 0);
x_270 = lean_ctor_get(x_207, 1);
x_271 = lean_ctor_get(x_207, 2);
x_272 = lean_ctor_get(x_207, 3);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_207);
x_273 = 1;
x_274 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_274, 0, x_269);
lean_ctor_set(x_274, 1, x_270);
lean_ctor_set(x_274, 2, x_271);
lean_ctor_set(x_274, 3, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*4, x_273);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_273);
x_275 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_274);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_275);
return x_1;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_276 = lean_ctor_get(x_206, 1);
x_277 = lean_ctor_get(x_206, 2);
x_278 = lean_ctor_get(x_206, 3);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_206);
x_279 = lean_ctor_get(x_207, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_207, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_207, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_207, 3);
lean_inc(x_282);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_283 = x_207;
} else {
 lean_dec_ref(x_207);
 x_283 = lean_box(0);
}
x_284 = 1;
if (lean_is_scalar(x_283)) {
 x_285 = lean_alloc_ctor(1, 4, 1);
} else {
 x_285 = x_283;
}
lean_ctor_set(x_285, 0, x_279);
lean_ctor_set(x_285, 1, x_280);
lean_ctor_set(x_285, 2, x_281);
lean_ctor_set(x_285, 3, x_282);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_284);
x_286 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_286, 0, x_278);
lean_ctor_set(x_286, 1, x_36);
lean_ctor_set(x_286, 2, x_37);
lean_ctor_set(x_286, 3, x_38);
lean_ctor_set_uint8(x_286, sizeof(void*)*4, x_284);
x_287 = 0;
lean_ctor_set(x_1, 3, x_286);
lean_ctor_set(x_1, 2, x_277);
lean_ctor_set(x_1, 1, x_276);
lean_ctor_set(x_1, 0, x_285);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_287);
return x_1;
}
}
else
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_206, 3);
lean_inc(x_288);
if (lean_obj_tag(x_288) == 0)
{
uint8_t x_289; 
x_289 = !lean_is_exclusive(x_206);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_293; 
x_290 = lean_ctor_get(x_206, 3);
lean_dec(x_290);
x_291 = lean_ctor_get(x_206, 0);
lean_dec(x_291);
x_292 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_292);
x_293 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_293);
return x_1;
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_206, 1);
x_295 = lean_ctor_get(x_206, 2);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_206);
x_296 = 0;
x_297 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_297, 0, x_207);
lean_ctor_set(x_297, 1, x_294);
lean_ctor_set(x_297, 2, x_295);
lean_ctor_set(x_297, 3, x_288);
lean_ctor_set_uint8(x_297, sizeof(void*)*4, x_296);
x_298 = 1;
lean_ctor_set(x_1, 0, x_297);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_298);
return x_1;
}
}
else
{
uint8_t x_299; 
x_299 = lean_ctor_get_uint8(x_288, sizeof(void*)*4);
if (x_299 == 0)
{
uint8_t x_300; 
lean_free_object(x_1);
x_300 = !lean_is_exclusive(x_206);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_301 = lean_ctor_get(x_206, 1);
x_302 = lean_ctor_get(x_206, 2);
x_303 = lean_ctor_get(x_206, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_206, 0);
lean_dec(x_304);
x_305 = !lean_is_exclusive(x_288);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_311; 
x_306 = lean_ctor_get(x_288, 0);
x_307 = lean_ctor_get(x_288, 1);
x_308 = lean_ctor_get(x_288, 2);
x_309 = lean_ctor_get(x_288, 3);
x_310 = 1;
lean_inc(x_207);
lean_ctor_set(x_288, 3, x_306);
lean_ctor_set(x_288, 2, x_302);
lean_ctor_set(x_288, 1, x_301);
lean_ctor_set(x_288, 0, x_207);
x_311 = !lean_is_exclusive(x_207);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_312 = lean_ctor_get(x_207, 3);
lean_dec(x_312);
x_313 = lean_ctor_get(x_207, 2);
lean_dec(x_313);
x_314 = lean_ctor_get(x_207, 1);
lean_dec(x_314);
x_315 = lean_ctor_get(x_207, 0);
lean_dec(x_315);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
lean_ctor_set(x_207, 3, x_38);
lean_ctor_set(x_207, 2, x_37);
lean_ctor_set(x_207, 1, x_36);
lean_ctor_set(x_207, 0, x_309);
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_310);
x_316 = 0;
lean_ctor_set(x_206, 3, x_207);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_316);
return x_206;
}
else
{
lean_object* x_317; uint8_t x_318; 
lean_dec(x_207);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
x_317 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_36);
lean_ctor_set(x_317, 2, x_37);
lean_ctor_set(x_317, 3, x_38);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_310);
x_318 = 0;
lean_ctor_set(x_206, 3, x_317);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_318);
return x_206;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_319 = lean_ctor_get(x_288, 0);
x_320 = lean_ctor_get(x_288, 1);
x_321 = lean_ctor_get(x_288, 2);
x_322 = lean_ctor_get(x_288, 3);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_288);
x_323 = 1;
lean_inc(x_207);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_207);
lean_ctor_set(x_324, 1, x_301);
lean_ctor_set(x_324, 2, x_302);
lean_ctor_set(x_324, 3, x_319);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_325 = x_207;
} else {
 lean_dec_ref(x_207);
 x_325 = lean_box(0);
}
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_323);
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 4, 1);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_322);
lean_ctor_set(x_326, 1, x_36);
lean_ctor_set(x_326, 2, x_37);
lean_ctor_set(x_326, 3, x_38);
lean_ctor_set_uint8(x_326, sizeof(void*)*4, x_323);
x_327 = 0;
lean_ctor_set(x_206, 3, x_326);
lean_ctor_set(x_206, 2, x_321);
lean_ctor_set(x_206, 1, x_320);
lean_ctor_set(x_206, 0, x_324);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_327);
return x_206;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; 
x_328 = lean_ctor_get(x_206, 1);
x_329 = lean_ctor_get(x_206, 2);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_206);
x_330 = lean_ctor_get(x_288, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_288, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_288, 2);
lean_inc(x_332);
x_333 = lean_ctor_get(x_288, 3);
lean_inc(x_333);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 lean_ctor_release(x_288, 2);
 lean_ctor_release(x_288, 3);
 x_334 = x_288;
} else {
 lean_dec_ref(x_288);
 x_334 = lean_box(0);
}
x_335 = 1;
lean_inc(x_207);
if (lean_is_scalar(x_334)) {
 x_336 = lean_alloc_ctor(1, 4, 1);
} else {
 x_336 = x_334;
}
lean_ctor_set(x_336, 0, x_207);
lean_ctor_set(x_336, 1, x_328);
lean_ctor_set(x_336, 2, x_329);
lean_ctor_set(x_336, 3, x_330);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_337 = x_207;
} else {
 lean_dec_ref(x_207);
 x_337 = lean_box(0);
}
lean_ctor_set_uint8(x_336, sizeof(void*)*4, x_335);
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_36);
lean_ctor_set(x_338, 2, x_37);
lean_ctor_set(x_338, 3, x_38);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_335);
x_339 = 0;
x_340 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_340, 0, x_336);
lean_ctor_set(x_340, 1, x_331);
lean_ctor_set(x_340, 2, x_332);
lean_ctor_set(x_340, 3, x_338);
lean_ctor_set_uint8(x_340, sizeof(void*)*4, x_339);
return x_340;
}
}
else
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_206);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_342 = lean_ctor_get(x_206, 3);
lean_dec(x_342);
x_343 = lean_ctor_get(x_206, 0);
lean_dec(x_343);
x_344 = !lean_is_exclusive(x_207);
if (x_344 == 0)
{
uint8_t x_345; uint8_t x_346; 
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_299);
x_345 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_345);
x_346 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_346);
return x_1;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; uint8_t x_353; 
x_347 = lean_ctor_get(x_207, 0);
x_348 = lean_ctor_get(x_207, 1);
x_349 = lean_ctor_get(x_207, 2);
x_350 = lean_ctor_get(x_207, 3);
lean_inc(x_350);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_207);
x_351 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_351, 0, x_347);
lean_ctor_set(x_351, 1, x_348);
lean_ctor_set(x_351, 2, x_349);
lean_ctor_set(x_351, 3, x_350);
lean_ctor_set_uint8(x_351, sizeof(void*)*4, x_299);
x_352 = 0;
lean_ctor_set(x_206, 0, x_351);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_352);
x_353 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_353);
return x_1;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; uint8_t x_364; 
x_354 = lean_ctor_get(x_206, 1);
x_355 = lean_ctor_get(x_206, 2);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_206);
x_356 = lean_ctor_get(x_207, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_207, 1);
lean_inc(x_357);
x_358 = lean_ctor_get(x_207, 2);
lean_inc(x_358);
x_359 = lean_ctor_get(x_207, 3);
lean_inc(x_359);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_360 = x_207;
} else {
 lean_dec_ref(x_207);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 4, 1);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_356);
lean_ctor_set(x_361, 1, x_357);
lean_ctor_set(x_361, 2, x_358);
lean_ctor_set(x_361, 3, x_359);
lean_ctor_set_uint8(x_361, sizeof(void*)*4, x_299);
x_362 = 0;
x_363 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_354);
lean_ctor_set(x_363, 2, x_355);
lean_ctor_set(x_363, 3, x_288);
lean_ctor_set_uint8(x_363, sizeof(void*)*4, x_362);
x_364 = 1;
lean_ctor_set(x_1, 0, x_363);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_364);
return x_1;
}
}
}
}
}
}
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_365 = lean_ctor_get(x_1, 0);
x_366 = lean_ctor_get(x_1, 1);
x_367 = lean_ctor_get(x_1, 2);
x_368 = lean_ctor_get(x_1, 3);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_1);
x_369 = l_Lean_Name_quickLt(x_2, x_366);
if (x_369 == 0)
{
uint8_t x_370; 
x_370 = l_Lean_Name_quickLt(x_366, x_2);
if (x_370 == 0)
{
uint8_t x_371; lean_object* x_372; 
lean_dec(x_367);
lean_dec(x_366);
x_371 = 1;
x_372 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_372, 0, x_365);
lean_ctor_set(x_372, 1, x_2);
lean_ctor_set(x_372, 2, x_3);
lean_ctor_set(x_372, 3, x_368);
lean_ctor_set_uint8(x_372, sizeof(void*)*4, x_371);
return x_372;
}
else
{
uint8_t x_373; 
x_373 = l_Std_RBNode_isRed___rarg(x_368);
if (x_373 == 0)
{
lean_object* x_374; uint8_t x_375; lean_object* x_376; 
x_374 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_368, x_2, x_3);
x_375 = 1;
x_376 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_376, 0, x_365);
lean_ctor_set(x_376, 1, x_366);
lean_ctor_set(x_376, 2, x_367);
lean_ctor_set(x_376, 3, x_374);
lean_ctor_set_uint8(x_376, sizeof(void*)*4, x_375);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; 
x_377 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_368, x_2, x_3);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_377, 3);
lean_inc(x_379);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; 
x_380 = lean_ctor_get(x_377, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_377, 2);
lean_inc(x_381);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_382 = x_377;
} else {
 lean_dec_ref(x_377);
 x_382 = lean_box(0);
}
x_383 = 0;
if (lean_is_scalar(x_382)) {
 x_384 = lean_alloc_ctor(1, 4, 1);
} else {
 x_384 = x_382;
}
lean_ctor_set(x_384, 0, x_379);
lean_ctor_set(x_384, 1, x_380);
lean_ctor_set(x_384, 2, x_381);
lean_ctor_set(x_384, 3, x_379);
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_383);
x_385 = 1;
x_386 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_386, 0, x_365);
lean_ctor_set(x_386, 1, x_366);
lean_ctor_set(x_386, 2, x_367);
lean_ctor_set(x_386, 3, x_384);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_385);
return x_386;
}
else
{
uint8_t x_387; 
x_387 = lean_ctor_get_uint8(x_379, sizeof(void*)*4);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; lean_object* x_400; 
x_388 = lean_ctor_get(x_377, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_377, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_390 = x_377;
} else {
 lean_dec_ref(x_377);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_379, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_379, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_379, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_379, 3);
lean_inc(x_394);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 lean_ctor_release(x_379, 2);
 lean_ctor_release(x_379, 3);
 x_395 = x_379;
} else {
 lean_dec_ref(x_379);
 x_395 = lean_box(0);
}
x_396 = 1;
if (lean_is_scalar(x_395)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_395;
}
lean_ctor_set(x_397, 0, x_365);
lean_ctor_set(x_397, 1, x_366);
lean_ctor_set(x_397, 2, x_367);
lean_ctor_set(x_397, 3, x_378);
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_396);
if (lean_is_scalar(x_390)) {
 x_398 = lean_alloc_ctor(1, 4, 1);
} else {
 x_398 = x_390;
}
lean_ctor_set(x_398, 0, x_391);
lean_ctor_set(x_398, 1, x_392);
lean_ctor_set(x_398, 2, x_393);
lean_ctor_set(x_398, 3, x_394);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_396);
x_399 = 0;
x_400 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_388);
lean_ctor_set(x_400, 2, x_389);
lean_ctor_set(x_400, 3, x_398);
lean_ctor_set_uint8(x_400, sizeof(void*)*4, x_399);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; 
x_401 = lean_ctor_get(x_377, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_377, 2);
lean_inc(x_402);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_403 = x_377;
} else {
 lean_dec_ref(x_377);
 x_403 = lean_box(0);
}
x_404 = 0;
if (lean_is_scalar(x_403)) {
 x_405 = lean_alloc_ctor(1, 4, 1);
} else {
 x_405 = x_403;
}
lean_ctor_set(x_405, 0, x_378);
lean_ctor_set(x_405, 1, x_401);
lean_ctor_set(x_405, 2, x_402);
lean_ctor_set(x_405, 3, x_379);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_404);
x_406 = 1;
x_407 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_407, 0, x_365);
lean_ctor_set(x_407, 1, x_366);
lean_ctor_set(x_407, 2, x_367);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
return x_407;
}
}
}
else
{
uint8_t x_408; 
x_408 = lean_ctor_get_uint8(x_378, sizeof(void*)*4);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; 
x_409 = lean_ctor_get(x_377, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_377, 2);
lean_inc(x_410);
x_411 = lean_ctor_get(x_377, 3);
lean_inc(x_411);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_412 = x_377;
} else {
 lean_dec_ref(x_377);
 x_412 = lean_box(0);
}
x_413 = lean_ctor_get(x_378, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_378, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_378, 2);
lean_inc(x_415);
x_416 = lean_ctor_get(x_378, 3);
lean_inc(x_416);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_417 = x_378;
} else {
 lean_dec_ref(x_378);
 x_417 = lean_box(0);
}
x_418 = 1;
if (lean_is_scalar(x_417)) {
 x_419 = lean_alloc_ctor(1, 4, 1);
} else {
 x_419 = x_417;
}
lean_ctor_set(x_419, 0, x_365);
lean_ctor_set(x_419, 1, x_366);
lean_ctor_set(x_419, 2, x_367);
lean_ctor_set(x_419, 3, x_413);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
if (lean_is_scalar(x_412)) {
 x_420 = lean_alloc_ctor(1, 4, 1);
} else {
 x_420 = x_412;
}
lean_ctor_set(x_420, 0, x_416);
lean_ctor_set(x_420, 1, x_409);
lean_ctor_set(x_420, 2, x_410);
lean_ctor_set(x_420, 3, x_411);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_418);
x_421 = 0;
x_422 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_414);
lean_ctor_set(x_422, 2, x_415);
lean_ctor_set(x_422, 3, x_420);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
return x_422;
}
else
{
lean_object* x_423; 
x_423 = lean_ctor_get(x_377, 3);
lean_inc(x_423);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; 
x_424 = lean_ctor_get(x_377, 1);
lean_inc(x_424);
x_425 = lean_ctor_get(x_377, 2);
lean_inc(x_425);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_426 = x_377;
} else {
 lean_dec_ref(x_377);
 x_426 = lean_box(0);
}
x_427 = 0;
if (lean_is_scalar(x_426)) {
 x_428 = lean_alloc_ctor(1, 4, 1);
} else {
 x_428 = x_426;
}
lean_ctor_set(x_428, 0, x_378);
lean_ctor_set(x_428, 1, x_424);
lean_ctor_set(x_428, 2, x_425);
lean_ctor_set(x_428, 3, x_423);
lean_ctor_set_uint8(x_428, sizeof(void*)*4, x_427);
x_429 = 1;
x_430 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_430, 0, x_365);
lean_ctor_set(x_430, 1, x_366);
lean_ctor_set(x_430, 2, x_367);
lean_ctor_set(x_430, 3, x_428);
lean_ctor_set_uint8(x_430, sizeof(void*)*4, x_429);
return x_430;
}
else
{
uint8_t x_431; 
x_431 = lean_ctor_get_uint8(x_423, sizeof(void*)*4);
if (x_431 == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; 
x_432 = lean_ctor_get(x_377, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_377, 2);
lean_inc(x_433);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_434 = x_377;
} else {
 lean_dec_ref(x_377);
 x_434 = lean_box(0);
}
x_435 = lean_ctor_get(x_423, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_423, 1);
lean_inc(x_436);
x_437 = lean_ctor_get(x_423, 2);
lean_inc(x_437);
x_438 = lean_ctor_get(x_423, 3);
lean_inc(x_438);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 lean_ctor_release(x_423, 2);
 lean_ctor_release(x_423, 3);
 x_439 = x_423;
} else {
 lean_dec_ref(x_423);
 x_439 = lean_box(0);
}
x_440 = 1;
lean_inc(x_378);
if (lean_is_scalar(x_439)) {
 x_441 = lean_alloc_ctor(1, 4, 1);
} else {
 x_441 = x_439;
}
lean_ctor_set(x_441, 0, x_365);
lean_ctor_set(x_441, 1, x_366);
lean_ctor_set(x_441, 2, x_367);
lean_ctor_set(x_441, 3, x_378);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_442 = x_378;
} else {
 lean_dec_ref(x_378);
 x_442 = lean_box(0);
}
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_440);
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_435);
lean_ctor_set(x_443, 1, x_436);
lean_ctor_set(x_443, 2, x_437);
lean_ctor_set(x_443, 3, x_438);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_440);
x_444 = 0;
if (lean_is_scalar(x_434)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_434;
}
lean_ctor_set(x_445, 0, x_441);
lean_ctor_set(x_445, 1, x_432);
lean_ctor_set(x_445, 2, x_433);
lean_ctor_set(x_445, 3, x_443);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_444);
return x_445;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; uint8_t x_457; lean_object* x_458; 
x_446 = lean_ctor_get(x_377, 1);
lean_inc(x_446);
x_447 = lean_ctor_get(x_377, 2);
lean_inc(x_447);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_448 = x_377;
} else {
 lean_dec_ref(x_377);
 x_448 = lean_box(0);
}
x_449 = lean_ctor_get(x_378, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_378, 1);
lean_inc(x_450);
x_451 = lean_ctor_get(x_378, 2);
lean_inc(x_451);
x_452 = lean_ctor_get(x_378, 3);
lean_inc(x_452);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_453 = x_378;
} else {
 lean_dec_ref(x_378);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 4, 1);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_449);
lean_ctor_set(x_454, 1, x_450);
lean_ctor_set(x_454, 2, x_451);
lean_ctor_set(x_454, 3, x_452);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_431);
x_455 = 0;
if (lean_is_scalar(x_448)) {
 x_456 = lean_alloc_ctor(1, 4, 1);
} else {
 x_456 = x_448;
}
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_446);
lean_ctor_set(x_456, 2, x_447);
lean_ctor_set(x_456, 3, x_423);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_455);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_365);
lean_ctor_set(x_458, 1, x_366);
lean_ctor_set(x_458, 2, x_367);
lean_ctor_set(x_458, 3, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
}
}
}
}
}
}
else
{
uint8_t x_459; 
x_459 = l_Std_RBNode_isRed___rarg(x_365);
if (x_459 == 0)
{
lean_object* x_460; uint8_t x_461; lean_object* x_462; 
x_460 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_365, x_2, x_3);
x_461 = 1;
x_462 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_366);
lean_ctor_set(x_462, 2, x_367);
lean_ctor_set(x_462, 3, x_368);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
return x_462;
}
else
{
lean_object* x_463; lean_object* x_464; 
x_463 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_365, x_2, x_3);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; 
x_465 = lean_ctor_get(x_463, 3);
lean_inc(x_465);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; lean_object* x_470; uint8_t x_471; lean_object* x_472; 
x_466 = lean_ctor_get(x_463, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_463, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_468 = x_463;
} else {
 lean_dec_ref(x_463);
 x_468 = lean_box(0);
}
x_469 = 0;
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(1, 4, 1);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_465);
lean_ctor_set(x_470, 1, x_466);
lean_ctor_set(x_470, 2, x_467);
lean_ctor_set(x_470, 3, x_465);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_469);
x_471 = 1;
x_472 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_366);
lean_ctor_set(x_472, 2, x_367);
lean_ctor_set(x_472, 3, x_368);
lean_ctor_set_uint8(x_472, sizeof(void*)*4, x_471);
return x_472;
}
else
{
uint8_t x_473; 
x_473 = lean_ctor_get_uint8(x_465, sizeof(void*)*4);
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; 
x_474 = lean_ctor_get(x_463, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_463, 2);
lean_inc(x_475);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_476 = x_463;
} else {
 lean_dec_ref(x_463);
 x_476 = lean_box(0);
}
x_477 = lean_ctor_get(x_465, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_465, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_465, 2);
lean_inc(x_479);
x_480 = lean_ctor_get(x_465, 3);
lean_inc(x_480);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 lean_ctor_release(x_465, 2);
 lean_ctor_release(x_465, 3);
 x_481 = x_465;
} else {
 lean_dec_ref(x_465);
 x_481 = lean_box(0);
}
x_482 = 1;
if (lean_is_scalar(x_481)) {
 x_483 = lean_alloc_ctor(1, 4, 1);
} else {
 x_483 = x_481;
}
lean_ctor_set(x_483, 0, x_464);
lean_ctor_set(x_483, 1, x_474);
lean_ctor_set(x_483, 2, x_475);
lean_ctor_set(x_483, 3, x_477);
lean_ctor_set_uint8(x_483, sizeof(void*)*4, x_482);
if (lean_is_scalar(x_476)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_476;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_366);
lean_ctor_set(x_484, 2, x_367);
lean_ctor_set(x_484, 3, x_368);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_482);
x_485 = 0;
x_486 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_478);
lean_ctor_set(x_486, 2, x_479);
lean_ctor_set(x_486, 3, x_484);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_485);
return x_486;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; lean_object* x_491; uint8_t x_492; lean_object* x_493; 
x_487 = lean_ctor_get(x_463, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_463, 2);
lean_inc(x_488);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_489 = x_463;
} else {
 lean_dec_ref(x_463);
 x_489 = lean_box(0);
}
x_490 = 0;
if (lean_is_scalar(x_489)) {
 x_491 = lean_alloc_ctor(1, 4, 1);
} else {
 x_491 = x_489;
}
lean_ctor_set(x_491, 0, x_464);
lean_ctor_set(x_491, 1, x_487);
lean_ctor_set(x_491, 2, x_488);
lean_ctor_set(x_491, 3, x_465);
lean_ctor_set_uint8(x_491, sizeof(void*)*4, x_490);
x_492 = 1;
x_493 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_366);
lean_ctor_set(x_493, 2, x_367);
lean_ctor_set(x_493, 3, x_368);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_492);
return x_493;
}
}
}
else
{
uint8_t x_494; 
x_494 = lean_ctor_get_uint8(x_464, sizeof(void*)*4);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; lean_object* x_508; 
x_495 = lean_ctor_get(x_463, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_463, 2);
lean_inc(x_496);
x_497 = lean_ctor_get(x_463, 3);
lean_inc(x_497);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_498 = x_463;
} else {
 lean_dec_ref(x_463);
 x_498 = lean_box(0);
}
x_499 = lean_ctor_get(x_464, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_464, 1);
lean_inc(x_500);
x_501 = lean_ctor_get(x_464, 2);
lean_inc(x_501);
x_502 = lean_ctor_get(x_464, 3);
lean_inc(x_502);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_503 = x_464;
} else {
 lean_dec_ref(x_464);
 x_503 = lean_box(0);
}
x_504 = 1;
if (lean_is_scalar(x_503)) {
 x_505 = lean_alloc_ctor(1, 4, 1);
} else {
 x_505 = x_503;
}
lean_ctor_set(x_505, 0, x_499);
lean_ctor_set(x_505, 1, x_500);
lean_ctor_set(x_505, 2, x_501);
lean_ctor_set(x_505, 3, x_502);
lean_ctor_set_uint8(x_505, sizeof(void*)*4, x_504);
if (lean_is_scalar(x_498)) {
 x_506 = lean_alloc_ctor(1, 4, 1);
} else {
 x_506 = x_498;
}
lean_ctor_set(x_506, 0, x_497);
lean_ctor_set(x_506, 1, x_366);
lean_ctor_set(x_506, 2, x_367);
lean_ctor_set(x_506, 3, x_368);
lean_ctor_set_uint8(x_506, sizeof(void*)*4, x_504);
x_507 = 0;
x_508 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_495);
lean_ctor_set(x_508, 2, x_496);
lean_ctor_set(x_508, 3, x_506);
lean_ctor_set_uint8(x_508, sizeof(void*)*4, x_507);
return x_508;
}
else
{
lean_object* x_509; 
x_509 = lean_ctor_get(x_463, 3);
lean_inc(x_509);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; lean_object* x_514; uint8_t x_515; lean_object* x_516; 
x_510 = lean_ctor_get(x_463, 1);
lean_inc(x_510);
x_511 = lean_ctor_get(x_463, 2);
lean_inc(x_511);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_512 = x_463;
} else {
 lean_dec_ref(x_463);
 x_512 = lean_box(0);
}
x_513 = 0;
if (lean_is_scalar(x_512)) {
 x_514 = lean_alloc_ctor(1, 4, 1);
} else {
 x_514 = x_512;
}
lean_ctor_set(x_514, 0, x_464);
lean_ctor_set(x_514, 1, x_510);
lean_ctor_set(x_514, 2, x_511);
lean_ctor_set(x_514, 3, x_509);
lean_ctor_set_uint8(x_514, sizeof(void*)*4, x_513);
x_515 = 1;
x_516 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_366);
lean_ctor_set(x_516, 2, x_367);
lean_ctor_set(x_516, 3, x_368);
lean_ctor_set_uint8(x_516, sizeof(void*)*4, x_515);
return x_516;
}
else
{
uint8_t x_517; 
x_517 = lean_ctor_get_uint8(x_509, sizeof(void*)*4);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; uint8_t x_530; lean_object* x_531; 
x_518 = lean_ctor_get(x_463, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_463, 2);
lean_inc(x_519);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_520 = x_463;
} else {
 lean_dec_ref(x_463);
 x_520 = lean_box(0);
}
x_521 = lean_ctor_get(x_509, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_509, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_509, 2);
lean_inc(x_523);
x_524 = lean_ctor_get(x_509, 3);
lean_inc(x_524);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 lean_ctor_release(x_509, 2);
 lean_ctor_release(x_509, 3);
 x_525 = x_509;
} else {
 lean_dec_ref(x_509);
 x_525 = lean_box(0);
}
x_526 = 1;
lean_inc(x_464);
if (lean_is_scalar(x_525)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_525;
}
lean_ctor_set(x_527, 0, x_464);
lean_ctor_set(x_527, 1, x_518);
lean_ctor_set(x_527, 2, x_519);
lean_ctor_set(x_527, 3, x_521);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_528 = x_464;
} else {
 lean_dec_ref(x_464);
 x_528 = lean_box(0);
}
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(1, 4, 1);
} else {
 x_529 = x_528;
}
lean_ctor_set(x_529, 0, x_524);
lean_ctor_set(x_529, 1, x_366);
lean_ctor_set(x_529, 2, x_367);
lean_ctor_set(x_529, 3, x_368);
lean_ctor_set_uint8(x_529, sizeof(void*)*4, x_526);
x_530 = 0;
if (lean_is_scalar(x_520)) {
 x_531 = lean_alloc_ctor(1, 4, 1);
} else {
 x_531 = x_520;
}
lean_ctor_set(x_531, 0, x_527);
lean_ctor_set(x_531, 1, x_522);
lean_ctor_set(x_531, 2, x_523);
lean_ctor_set(x_531, 3, x_529);
lean_ctor_set_uint8(x_531, sizeof(void*)*4, x_530);
return x_531;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; uint8_t x_543; lean_object* x_544; 
x_532 = lean_ctor_get(x_463, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_463, 2);
lean_inc(x_533);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_534 = x_463;
} else {
 lean_dec_ref(x_463);
 x_534 = lean_box(0);
}
x_535 = lean_ctor_get(x_464, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_464, 1);
lean_inc(x_536);
x_537 = lean_ctor_get(x_464, 2);
lean_inc(x_537);
x_538 = lean_ctor_get(x_464, 3);
lean_inc(x_538);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_539 = x_464;
} else {
 lean_dec_ref(x_464);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 4, 1);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_535);
lean_ctor_set(x_540, 1, x_536);
lean_ctor_set(x_540, 2, x_537);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_517);
x_541 = 0;
if (lean_is_scalar(x_534)) {
 x_542 = lean_alloc_ctor(1, 4, 1);
} else {
 x_542 = x_534;
}
lean_ctor_set(x_542, 0, x_540);
lean_ctor_set(x_542, 1, x_532);
lean_ctor_set(x_542, 2, x_533);
lean_ctor_set(x_542, 3, x_509);
lean_ctor_set_uint8(x_542, sizeof(void*)*4, x_541);
x_543 = 1;
x_544 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_366);
lean_ctor_set(x_544, 2, x_367);
lean_ctor_set(x_544, 3, x_368);
lean_ctor_set_uint8(x_544, sizeof(void*)*4, x_543);
return x_544;
}
}
}
}
}
}
}
}
}
}
}
lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = l_Lean_Name_quickLt(x_2, x_10);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Name_quickLt(x_10, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_10);
x_15 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_12, x_2, x_3);
x_17 = 0;
lean_ctor_set(x_1, 3, x_16);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_17);
return x_1;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_9, x_2, x_3);
x_19 = 0;
lean_ctor_set(x_1, 0, x_18);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = l_Lean_Name_quickLt(x_2, x_21);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Name_quickLt(x_21, x_2);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_21);
x_26 = 0;
x_27 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set(x_27, 2, x_3);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_26);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_23, x_2, x_3);
x_29 = 0;
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_22);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_29);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_20, x_2, x_3);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = l_Lean_Name_quickLt(x_2, x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Name_quickLt(x_36, x_2);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_37);
lean_dec(x_36);
x_41 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_41);
return x_1;
}
else
{
uint8_t x_42; 
x_42 = l_Std_RBNode_isRed___rarg(x_38);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_38, x_2, x_3);
x_44 = 1;
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_44);
return x_1;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_38, x_2, x_3);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 3);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_45, 3);
lean_dec(x_49);
x_50 = lean_ctor_get(x_45, 0);
lean_dec(x_50);
x_51 = 0;
lean_ctor_set(x_45, 0, x_47);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_51);
x_52 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_52);
return x_1;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_45, 1);
x_54 = lean_ctor_get(x_45, 2);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_45);
x_55 = 0;
x_56 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_56, 2, x_54);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_55);
x_57 = 1;
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_57);
return x_1;
}
}
else
{
uint8_t x_58; 
x_58 = lean_ctor_get_uint8(x_47, sizeof(void*)*4);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_45);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_45, 1);
x_61 = lean_ctor_get(x_45, 2);
x_62 = lean_ctor_get(x_45, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_45, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_47);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_47, 0);
x_66 = lean_ctor_get(x_47, 1);
x_67 = lean_ctor_get(x_47, 2);
x_68 = lean_ctor_get(x_47, 3);
x_69 = 1;
lean_ctor_set(x_47, 3, x_46);
lean_ctor_set(x_47, 2, x_37);
lean_ctor_set(x_47, 1, x_36);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_69);
lean_ctor_set(x_45, 3, x_68);
lean_ctor_set(x_45, 2, x_67);
lean_ctor_set(x_45, 1, x_66);
lean_ctor_set(x_45, 0, x_65);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_69);
x_70 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_61);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_1, 0, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_70);
return x_1;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; 
x_71 = lean_ctor_get(x_47, 0);
x_72 = lean_ctor_get(x_47, 1);
x_73 = lean_ctor_get(x_47, 2);
x_74 = lean_ctor_get(x_47, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_47);
x_75 = 1;
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_35);
lean_ctor_set(x_76, 1, x_36);
lean_ctor_set(x_76, 2, x_37);
lean_ctor_set(x_76, 3, x_46);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_75);
lean_ctor_set(x_45, 3, x_74);
lean_ctor_set(x_45, 2, x_73);
lean_ctor_set(x_45, 1, x_72);
lean_ctor_set(x_45, 0, x_71);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_75);
x_77 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_61);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_1, 0, x_76);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_77);
return x_1;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_78 = lean_ctor_get(x_45, 1);
x_79 = lean_ctor_get(x_45, 2);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_45);
x_80 = lean_ctor_get(x_47, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_47, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_47, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_47, 3);
lean_inc(x_83);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_84 = x_47;
} else {
 lean_dec_ref(x_47);
 x_84 = lean_box(0);
}
x_85 = 1;
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(1, 4, 1);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_35);
lean_ctor_set(x_86, 1, x_36);
lean_ctor_set(x_86, 2, x_37);
lean_ctor_set(x_86, 3, x_46);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_85);
x_87 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_81);
lean_ctor_set(x_87, 2, x_82);
lean_ctor_set(x_87, 3, x_83);
lean_ctor_set_uint8(x_87, sizeof(void*)*4, x_85);
x_88 = 0;
lean_ctor_set(x_1, 3, x_87);
lean_ctor_set(x_1, 2, x_79);
lean_ctor_set(x_1, 1, x_78);
lean_ctor_set(x_1, 0, x_86);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_88);
return x_1;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_45);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_45, 3);
lean_dec(x_90);
x_91 = lean_ctor_get(x_45, 0);
lean_dec(x_91);
x_92 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_92);
x_93 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_93);
return x_1;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_45, 1);
x_95 = lean_ctor_get(x_45, 2);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_45);
x_96 = 0;
x_97 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_97, 0, x_46);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_47);
lean_ctor_set_uint8(x_97, sizeof(void*)*4, x_96);
x_98 = 1;
lean_ctor_set(x_1, 3, x_97);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_98);
return x_1;
}
}
}
}
else
{
uint8_t x_99; 
x_99 = lean_ctor_get_uint8(x_46, sizeof(void*)*4);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_45);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_45, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_46);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; 
x_103 = lean_ctor_get(x_46, 0);
x_104 = lean_ctor_get(x_46, 1);
x_105 = lean_ctor_get(x_46, 2);
x_106 = lean_ctor_get(x_46, 3);
x_107 = 1;
lean_ctor_set(x_46, 3, x_103);
lean_ctor_set(x_46, 2, x_37);
lean_ctor_set(x_46, 1, x_36);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_107);
lean_ctor_set(x_45, 0, x_106);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_107);
x_108 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_105);
lean_ctor_set(x_1, 1, x_104);
lean_ctor_set(x_1, 0, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_108);
return x_1;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; uint8_t x_115; 
x_109 = lean_ctor_get(x_46, 0);
x_110 = lean_ctor_get(x_46, 1);
x_111 = lean_ctor_get(x_46, 2);
x_112 = lean_ctor_get(x_46, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_46);
x_113 = 1;
x_114 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_114, 0, x_35);
lean_ctor_set(x_114, 1, x_36);
lean_ctor_set(x_114, 2, x_37);
lean_ctor_set(x_114, 3, x_109);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_113);
lean_ctor_set(x_45, 0, x_112);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_113);
x_115 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_111);
lean_ctor_set(x_1, 1, x_110);
lean_ctor_set(x_1, 0, x_114);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_115);
return x_1;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_116 = lean_ctor_get(x_45, 1);
x_117 = lean_ctor_get(x_45, 2);
x_118 = lean_ctor_get(x_45, 3);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_45);
x_119 = lean_ctor_get(x_46, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_46, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_46, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_46, 3);
lean_inc(x_122);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_123 = x_46;
} else {
 lean_dec_ref(x_46);
 x_123 = lean_box(0);
}
x_124 = 1;
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(1, 4, 1);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_35);
lean_ctor_set(x_125, 1, x_36);
lean_ctor_set(x_125, 2, x_37);
lean_ctor_set(x_125, 3, x_119);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_124);
x_126 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_116);
lean_ctor_set(x_126, 2, x_117);
lean_ctor_set(x_126, 3, x_118);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_124);
x_127 = 0;
lean_ctor_set(x_1, 3, x_126);
lean_ctor_set(x_1, 2, x_121);
lean_ctor_set(x_1, 1, x_120);
lean_ctor_set(x_1, 0, x_125);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_127);
return x_1;
}
}
else
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_45, 3);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_45);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_45, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_45, 0);
lean_dec(x_131);
x_132 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_132);
x_133 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_133);
return x_1;
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; uint8_t x_138; 
x_134 = lean_ctor_get(x_45, 1);
x_135 = lean_ctor_get(x_45, 2);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_45);
x_136 = 0;
x_137 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_137, 0, x_46);
lean_ctor_set(x_137, 1, x_134);
lean_ctor_set(x_137, 2, x_135);
lean_ctor_set(x_137, 3, x_128);
lean_ctor_set_uint8(x_137, sizeof(void*)*4, x_136);
x_138 = 1;
lean_ctor_set(x_1, 3, x_137);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_138);
return x_1;
}
}
else
{
uint8_t x_139; 
x_139 = lean_ctor_get_uint8(x_128, sizeof(void*)*4);
if (x_139 == 0)
{
uint8_t x_140; 
lean_free_object(x_1);
x_140 = !lean_is_exclusive(x_45);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_45, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_45, 0);
lean_dec(x_142);
x_143 = !lean_is_exclusive(x_128);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; 
x_144 = lean_ctor_get(x_128, 0);
x_145 = lean_ctor_get(x_128, 1);
x_146 = lean_ctor_get(x_128, 2);
x_147 = lean_ctor_get(x_128, 3);
x_148 = 1;
lean_inc(x_46);
lean_ctor_set(x_128, 3, x_46);
lean_ctor_set(x_128, 2, x_37);
lean_ctor_set(x_128, 1, x_36);
lean_ctor_set(x_128, 0, x_35);
x_149 = !lean_is_exclusive(x_46);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_150 = lean_ctor_get(x_46, 3);
lean_dec(x_150);
x_151 = lean_ctor_get(x_46, 2);
lean_dec(x_151);
x_152 = lean_ctor_get(x_46, 1);
lean_dec(x_152);
x_153 = lean_ctor_get(x_46, 0);
lean_dec(x_153);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_148);
lean_ctor_set(x_46, 3, x_147);
lean_ctor_set(x_46, 2, x_146);
lean_ctor_set(x_46, 1, x_145);
lean_ctor_set(x_46, 0, x_144);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_148);
x_154 = 0;
lean_ctor_set(x_45, 3, x_46);
lean_ctor_set(x_45, 0, x_128);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_154);
return x_45;
}
else
{
lean_object* x_155; uint8_t x_156; 
lean_dec(x_46);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_148);
x_155 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_155, 0, x_144);
lean_ctor_set(x_155, 1, x_145);
lean_ctor_set(x_155, 2, x_146);
lean_ctor_set(x_155, 3, x_147);
lean_ctor_set_uint8(x_155, sizeof(void*)*4, x_148);
x_156 = 0;
lean_ctor_set(x_45, 3, x_155);
lean_ctor_set(x_45, 0, x_128);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_156);
return x_45;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_157 = lean_ctor_get(x_128, 0);
x_158 = lean_ctor_get(x_128, 1);
x_159 = lean_ctor_get(x_128, 2);
x_160 = lean_ctor_get(x_128, 3);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_128);
x_161 = 1;
lean_inc(x_46);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_35);
lean_ctor_set(x_162, 1, x_36);
lean_ctor_set(x_162, 2, x_37);
lean_ctor_set(x_162, 3, x_46);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_163 = x_46;
} else {
 lean_dec_ref(x_46);
 x_163 = lean_box(0);
}
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_161);
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 4, 1);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_157);
lean_ctor_set(x_164, 1, x_158);
lean_ctor_set(x_164, 2, x_159);
lean_ctor_set(x_164, 3, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_161);
x_165 = 0;
lean_ctor_set(x_45, 3, x_164);
lean_ctor_set(x_45, 0, x_162);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_165);
return x_45;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; 
x_166 = lean_ctor_get(x_45, 1);
x_167 = lean_ctor_get(x_45, 2);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_45);
x_168 = lean_ctor_get(x_128, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_128, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_128, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_128, 3);
lean_inc(x_171);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 x_172 = x_128;
} else {
 lean_dec_ref(x_128);
 x_172 = lean_box(0);
}
x_173 = 1;
lean_inc(x_46);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(1, 4, 1);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_35);
lean_ctor_set(x_174, 1, x_36);
lean_ctor_set(x_174, 2, x_37);
lean_ctor_set(x_174, 3, x_46);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_175 = x_46;
} else {
 lean_dec_ref(x_46);
 x_175 = lean_box(0);
}
lean_ctor_set_uint8(x_174, sizeof(void*)*4, x_173);
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 4, 1);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_168);
lean_ctor_set(x_176, 1, x_169);
lean_ctor_set(x_176, 2, x_170);
lean_ctor_set(x_176, 3, x_171);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_173);
x_177 = 0;
x_178 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_166);
lean_ctor_set(x_178, 2, x_167);
lean_ctor_set(x_178, 3, x_176);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_177);
return x_178;
}
}
else
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_45);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_45, 3);
lean_dec(x_180);
x_181 = lean_ctor_get(x_45, 0);
lean_dec(x_181);
x_182 = !lean_is_exclusive(x_46);
if (x_182 == 0)
{
uint8_t x_183; uint8_t x_184; 
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_139);
x_183 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_183);
x_184 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_184);
return x_1;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_191; 
x_185 = lean_ctor_get(x_46, 0);
x_186 = lean_ctor_get(x_46, 1);
x_187 = lean_ctor_get(x_46, 2);
x_188 = lean_ctor_get(x_46, 3);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_46);
x_189 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_189, 0, x_185);
lean_ctor_set(x_189, 1, x_186);
lean_ctor_set(x_189, 2, x_187);
lean_ctor_set(x_189, 3, x_188);
lean_ctor_set_uint8(x_189, sizeof(void*)*4, x_139);
x_190 = 0;
lean_ctor_set(x_45, 0, x_189);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_190);
x_191 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_191);
return x_1;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; uint8_t x_202; 
x_192 = lean_ctor_get(x_45, 1);
x_193 = lean_ctor_get(x_45, 2);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_45);
x_194 = lean_ctor_get(x_46, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_46, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_46, 2);
lean_inc(x_196);
x_197 = lean_ctor_get(x_46, 3);
lean_inc(x_197);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_198 = x_46;
} else {
 lean_dec_ref(x_46);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 4, 1);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_194);
lean_ctor_set(x_199, 1, x_195);
lean_ctor_set(x_199, 2, x_196);
lean_ctor_set(x_199, 3, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_139);
x_200 = 0;
x_201 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_192);
lean_ctor_set(x_201, 2, x_193);
lean_ctor_set(x_201, 3, x_128);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_200);
x_202 = 1;
lean_ctor_set(x_1, 3, x_201);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
}
}
}
}
}
}
}
}
else
{
uint8_t x_203; 
x_203 = l_Std_RBNode_isRed___rarg(x_35);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_35, x_2, x_3);
x_205 = 1;
lean_ctor_set(x_1, 0, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_205);
return x_1;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_35, x_2, x_3);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_206, 3);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_206);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; uint8_t x_213; 
x_210 = lean_ctor_get(x_206, 3);
lean_dec(x_210);
x_211 = lean_ctor_get(x_206, 0);
lean_dec(x_211);
x_212 = 0;
lean_ctor_set(x_206, 0, x_208);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_212);
x_213 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_213);
return x_1;
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_206, 1);
x_215 = lean_ctor_get(x_206, 2);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_206);
x_216 = 0;
x_217 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_217, 0, x_208);
lean_ctor_set(x_217, 1, x_214);
lean_ctor_set(x_217, 2, x_215);
lean_ctor_set(x_217, 3, x_208);
lean_ctor_set_uint8(x_217, sizeof(void*)*4, x_216);
x_218 = 1;
lean_ctor_set(x_1, 0, x_217);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_218);
return x_1;
}
}
else
{
uint8_t x_219; 
x_219 = lean_ctor_get_uint8(x_208, sizeof(void*)*4);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_206);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_221 = lean_ctor_get(x_206, 1);
x_222 = lean_ctor_get(x_206, 2);
x_223 = lean_ctor_get(x_206, 3);
lean_dec(x_223);
x_224 = lean_ctor_get(x_206, 0);
lean_dec(x_224);
x_225 = !lean_is_exclusive(x_208);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_231; 
x_226 = lean_ctor_get(x_208, 0);
x_227 = lean_ctor_get(x_208, 1);
x_228 = lean_ctor_get(x_208, 2);
x_229 = lean_ctor_get(x_208, 3);
x_230 = 1;
lean_ctor_set(x_208, 3, x_226);
lean_ctor_set(x_208, 2, x_222);
lean_ctor_set(x_208, 1, x_221);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_230);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_229);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_230);
x_231 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_208);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_231);
return x_1;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; uint8_t x_238; 
x_232 = lean_ctor_get(x_208, 0);
x_233 = lean_ctor_get(x_208, 1);
x_234 = lean_ctor_get(x_208, 2);
x_235 = lean_ctor_get(x_208, 3);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_208);
x_236 = 1;
x_237 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_237, 0, x_207);
lean_ctor_set(x_237, 1, x_221);
lean_ctor_set(x_237, 2, x_222);
lean_ctor_set(x_237, 3, x_232);
lean_ctor_set_uint8(x_237, sizeof(void*)*4, x_236);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_235);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_236);
x_238 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_234);
lean_ctor_set(x_1, 1, x_233);
lean_ctor_set(x_1, 0, x_237);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_238);
return x_1;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_239 = lean_ctor_get(x_206, 1);
x_240 = lean_ctor_get(x_206, 2);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_206);
x_241 = lean_ctor_get(x_208, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_208, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_208, 2);
lean_inc(x_243);
x_244 = lean_ctor_get(x_208, 3);
lean_inc(x_244);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 lean_ctor_release(x_208, 3);
 x_245 = x_208;
} else {
 lean_dec_ref(x_208);
 x_245 = lean_box(0);
}
x_246 = 1;
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(1, 4, 1);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_207);
lean_ctor_set(x_247, 1, x_239);
lean_ctor_set(x_247, 2, x_240);
lean_ctor_set(x_247, 3, x_241);
lean_ctor_set_uint8(x_247, sizeof(void*)*4, x_246);
x_248 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_248, 0, x_244);
lean_ctor_set(x_248, 1, x_36);
lean_ctor_set(x_248, 2, x_37);
lean_ctor_set(x_248, 3, x_38);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_246);
x_249 = 0;
lean_ctor_set(x_1, 3, x_248);
lean_ctor_set(x_1, 2, x_243);
lean_ctor_set(x_1, 1, x_242);
lean_ctor_set(x_1, 0, x_247);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_249);
return x_1;
}
}
else
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_206);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_254; 
x_251 = lean_ctor_get(x_206, 3);
lean_dec(x_251);
x_252 = lean_ctor_get(x_206, 0);
lean_dec(x_252);
x_253 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_253);
x_254 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_254);
return x_1;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_255 = lean_ctor_get(x_206, 1);
x_256 = lean_ctor_get(x_206, 2);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_206);
x_257 = 0;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_207);
lean_ctor_set(x_258, 1, x_255);
lean_ctor_set(x_258, 2, x_256);
lean_ctor_set(x_258, 3, x_208);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
x_259 = 1;
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
else
{
uint8_t x_260; 
x_260 = lean_ctor_get_uint8(x_207, sizeof(void*)*4);
if (x_260 == 0)
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_206);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_262 = lean_ctor_get(x_206, 1);
x_263 = lean_ctor_get(x_206, 2);
x_264 = lean_ctor_get(x_206, 3);
x_265 = lean_ctor_get(x_206, 0);
lean_dec(x_265);
x_266 = !lean_is_exclusive(x_207);
if (x_266 == 0)
{
uint8_t x_267; uint8_t x_268; 
x_267 = 1;
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_267);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_267);
x_268 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_207);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_268);
return x_1;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; uint8_t x_275; 
x_269 = lean_ctor_get(x_207, 0);
x_270 = lean_ctor_get(x_207, 1);
x_271 = lean_ctor_get(x_207, 2);
x_272 = lean_ctor_get(x_207, 3);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_207);
x_273 = 1;
x_274 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_274, 0, x_269);
lean_ctor_set(x_274, 1, x_270);
lean_ctor_set(x_274, 2, x_271);
lean_ctor_set(x_274, 3, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*4, x_273);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_273);
x_275 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_274);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_275);
return x_1;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_276 = lean_ctor_get(x_206, 1);
x_277 = lean_ctor_get(x_206, 2);
x_278 = lean_ctor_get(x_206, 3);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_206);
x_279 = lean_ctor_get(x_207, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_207, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_207, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_207, 3);
lean_inc(x_282);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_283 = x_207;
} else {
 lean_dec_ref(x_207);
 x_283 = lean_box(0);
}
x_284 = 1;
if (lean_is_scalar(x_283)) {
 x_285 = lean_alloc_ctor(1, 4, 1);
} else {
 x_285 = x_283;
}
lean_ctor_set(x_285, 0, x_279);
lean_ctor_set(x_285, 1, x_280);
lean_ctor_set(x_285, 2, x_281);
lean_ctor_set(x_285, 3, x_282);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_284);
x_286 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_286, 0, x_278);
lean_ctor_set(x_286, 1, x_36);
lean_ctor_set(x_286, 2, x_37);
lean_ctor_set(x_286, 3, x_38);
lean_ctor_set_uint8(x_286, sizeof(void*)*4, x_284);
x_287 = 0;
lean_ctor_set(x_1, 3, x_286);
lean_ctor_set(x_1, 2, x_277);
lean_ctor_set(x_1, 1, x_276);
lean_ctor_set(x_1, 0, x_285);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_287);
return x_1;
}
}
else
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_206, 3);
lean_inc(x_288);
if (lean_obj_tag(x_288) == 0)
{
uint8_t x_289; 
x_289 = !lean_is_exclusive(x_206);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_293; 
x_290 = lean_ctor_get(x_206, 3);
lean_dec(x_290);
x_291 = lean_ctor_get(x_206, 0);
lean_dec(x_291);
x_292 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_292);
x_293 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_293);
return x_1;
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_206, 1);
x_295 = lean_ctor_get(x_206, 2);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_206);
x_296 = 0;
x_297 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_297, 0, x_207);
lean_ctor_set(x_297, 1, x_294);
lean_ctor_set(x_297, 2, x_295);
lean_ctor_set(x_297, 3, x_288);
lean_ctor_set_uint8(x_297, sizeof(void*)*4, x_296);
x_298 = 1;
lean_ctor_set(x_1, 0, x_297);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_298);
return x_1;
}
}
else
{
uint8_t x_299; 
x_299 = lean_ctor_get_uint8(x_288, sizeof(void*)*4);
if (x_299 == 0)
{
uint8_t x_300; 
lean_free_object(x_1);
x_300 = !lean_is_exclusive(x_206);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_301 = lean_ctor_get(x_206, 1);
x_302 = lean_ctor_get(x_206, 2);
x_303 = lean_ctor_get(x_206, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_206, 0);
lean_dec(x_304);
x_305 = !lean_is_exclusive(x_288);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_311; 
x_306 = lean_ctor_get(x_288, 0);
x_307 = lean_ctor_get(x_288, 1);
x_308 = lean_ctor_get(x_288, 2);
x_309 = lean_ctor_get(x_288, 3);
x_310 = 1;
lean_inc(x_207);
lean_ctor_set(x_288, 3, x_306);
lean_ctor_set(x_288, 2, x_302);
lean_ctor_set(x_288, 1, x_301);
lean_ctor_set(x_288, 0, x_207);
x_311 = !lean_is_exclusive(x_207);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_312 = lean_ctor_get(x_207, 3);
lean_dec(x_312);
x_313 = lean_ctor_get(x_207, 2);
lean_dec(x_313);
x_314 = lean_ctor_get(x_207, 1);
lean_dec(x_314);
x_315 = lean_ctor_get(x_207, 0);
lean_dec(x_315);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
lean_ctor_set(x_207, 3, x_38);
lean_ctor_set(x_207, 2, x_37);
lean_ctor_set(x_207, 1, x_36);
lean_ctor_set(x_207, 0, x_309);
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_310);
x_316 = 0;
lean_ctor_set(x_206, 3, x_207);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_316);
return x_206;
}
else
{
lean_object* x_317; uint8_t x_318; 
lean_dec(x_207);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
x_317 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_36);
lean_ctor_set(x_317, 2, x_37);
lean_ctor_set(x_317, 3, x_38);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_310);
x_318 = 0;
lean_ctor_set(x_206, 3, x_317);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_318);
return x_206;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_319 = lean_ctor_get(x_288, 0);
x_320 = lean_ctor_get(x_288, 1);
x_321 = lean_ctor_get(x_288, 2);
x_322 = lean_ctor_get(x_288, 3);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_288);
x_323 = 1;
lean_inc(x_207);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_207);
lean_ctor_set(x_324, 1, x_301);
lean_ctor_set(x_324, 2, x_302);
lean_ctor_set(x_324, 3, x_319);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_325 = x_207;
} else {
 lean_dec_ref(x_207);
 x_325 = lean_box(0);
}
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_323);
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 4, 1);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_322);
lean_ctor_set(x_326, 1, x_36);
lean_ctor_set(x_326, 2, x_37);
lean_ctor_set(x_326, 3, x_38);
lean_ctor_set_uint8(x_326, sizeof(void*)*4, x_323);
x_327 = 0;
lean_ctor_set(x_206, 3, x_326);
lean_ctor_set(x_206, 2, x_321);
lean_ctor_set(x_206, 1, x_320);
lean_ctor_set(x_206, 0, x_324);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_327);
return x_206;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; 
x_328 = lean_ctor_get(x_206, 1);
x_329 = lean_ctor_get(x_206, 2);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_206);
x_330 = lean_ctor_get(x_288, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_288, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_288, 2);
lean_inc(x_332);
x_333 = lean_ctor_get(x_288, 3);
lean_inc(x_333);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 lean_ctor_release(x_288, 2);
 lean_ctor_release(x_288, 3);
 x_334 = x_288;
} else {
 lean_dec_ref(x_288);
 x_334 = lean_box(0);
}
x_335 = 1;
lean_inc(x_207);
if (lean_is_scalar(x_334)) {
 x_336 = lean_alloc_ctor(1, 4, 1);
} else {
 x_336 = x_334;
}
lean_ctor_set(x_336, 0, x_207);
lean_ctor_set(x_336, 1, x_328);
lean_ctor_set(x_336, 2, x_329);
lean_ctor_set(x_336, 3, x_330);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_337 = x_207;
} else {
 lean_dec_ref(x_207);
 x_337 = lean_box(0);
}
lean_ctor_set_uint8(x_336, sizeof(void*)*4, x_335);
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_36);
lean_ctor_set(x_338, 2, x_37);
lean_ctor_set(x_338, 3, x_38);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_335);
x_339 = 0;
x_340 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_340, 0, x_336);
lean_ctor_set(x_340, 1, x_331);
lean_ctor_set(x_340, 2, x_332);
lean_ctor_set(x_340, 3, x_338);
lean_ctor_set_uint8(x_340, sizeof(void*)*4, x_339);
return x_340;
}
}
else
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_206);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_342 = lean_ctor_get(x_206, 3);
lean_dec(x_342);
x_343 = lean_ctor_get(x_206, 0);
lean_dec(x_343);
x_344 = !lean_is_exclusive(x_207);
if (x_344 == 0)
{
uint8_t x_345; uint8_t x_346; 
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_299);
x_345 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_345);
x_346 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_346);
return x_1;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; uint8_t x_353; 
x_347 = lean_ctor_get(x_207, 0);
x_348 = lean_ctor_get(x_207, 1);
x_349 = lean_ctor_get(x_207, 2);
x_350 = lean_ctor_get(x_207, 3);
lean_inc(x_350);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_207);
x_351 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_351, 0, x_347);
lean_ctor_set(x_351, 1, x_348);
lean_ctor_set(x_351, 2, x_349);
lean_ctor_set(x_351, 3, x_350);
lean_ctor_set_uint8(x_351, sizeof(void*)*4, x_299);
x_352 = 0;
lean_ctor_set(x_206, 0, x_351);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_352);
x_353 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_353);
return x_1;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; uint8_t x_364; 
x_354 = lean_ctor_get(x_206, 1);
x_355 = lean_ctor_get(x_206, 2);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_206);
x_356 = lean_ctor_get(x_207, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_207, 1);
lean_inc(x_357);
x_358 = lean_ctor_get(x_207, 2);
lean_inc(x_358);
x_359 = lean_ctor_get(x_207, 3);
lean_inc(x_359);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_360 = x_207;
} else {
 lean_dec_ref(x_207);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 4, 1);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_356);
lean_ctor_set(x_361, 1, x_357);
lean_ctor_set(x_361, 2, x_358);
lean_ctor_set(x_361, 3, x_359);
lean_ctor_set_uint8(x_361, sizeof(void*)*4, x_299);
x_362 = 0;
x_363 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_354);
lean_ctor_set(x_363, 2, x_355);
lean_ctor_set(x_363, 3, x_288);
lean_ctor_set_uint8(x_363, sizeof(void*)*4, x_362);
x_364 = 1;
lean_ctor_set(x_1, 0, x_363);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_364);
return x_1;
}
}
}
}
}
}
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_365 = lean_ctor_get(x_1, 0);
x_366 = lean_ctor_get(x_1, 1);
x_367 = lean_ctor_get(x_1, 2);
x_368 = lean_ctor_get(x_1, 3);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_1);
x_369 = l_Lean_Name_quickLt(x_2, x_366);
if (x_369 == 0)
{
uint8_t x_370; 
x_370 = l_Lean_Name_quickLt(x_366, x_2);
if (x_370 == 0)
{
uint8_t x_371; lean_object* x_372; 
lean_dec(x_367);
lean_dec(x_366);
x_371 = 1;
x_372 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_372, 0, x_365);
lean_ctor_set(x_372, 1, x_2);
lean_ctor_set(x_372, 2, x_3);
lean_ctor_set(x_372, 3, x_368);
lean_ctor_set_uint8(x_372, sizeof(void*)*4, x_371);
return x_372;
}
else
{
uint8_t x_373; 
x_373 = l_Std_RBNode_isRed___rarg(x_368);
if (x_373 == 0)
{
lean_object* x_374; uint8_t x_375; lean_object* x_376; 
x_374 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_368, x_2, x_3);
x_375 = 1;
x_376 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_376, 0, x_365);
lean_ctor_set(x_376, 1, x_366);
lean_ctor_set(x_376, 2, x_367);
lean_ctor_set(x_376, 3, x_374);
lean_ctor_set_uint8(x_376, sizeof(void*)*4, x_375);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; 
x_377 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_368, x_2, x_3);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_377, 3);
lean_inc(x_379);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; 
x_380 = lean_ctor_get(x_377, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_377, 2);
lean_inc(x_381);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_382 = x_377;
} else {
 lean_dec_ref(x_377);
 x_382 = lean_box(0);
}
x_383 = 0;
if (lean_is_scalar(x_382)) {
 x_384 = lean_alloc_ctor(1, 4, 1);
} else {
 x_384 = x_382;
}
lean_ctor_set(x_384, 0, x_379);
lean_ctor_set(x_384, 1, x_380);
lean_ctor_set(x_384, 2, x_381);
lean_ctor_set(x_384, 3, x_379);
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_383);
x_385 = 1;
x_386 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_386, 0, x_365);
lean_ctor_set(x_386, 1, x_366);
lean_ctor_set(x_386, 2, x_367);
lean_ctor_set(x_386, 3, x_384);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_385);
return x_386;
}
else
{
uint8_t x_387; 
x_387 = lean_ctor_get_uint8(x_379, sizeof(void*)*4);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; lean_object* x_400; 
x_388 = lean_ctor_get(x_377, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_377, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_390 = x_377;
} else {
 lean_dec_ref(x_377);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_379, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_379, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_379, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_379, 3);
lean_inc(x_394);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 lean_ctor_release(x_379, 2);
 lean_ctor_release(x_379, 3);
 x_395 = x_379;
} else {
 lean_dec_ref(x_379);
 x_395 = lean_box(0);
}
x_396 = 1;
if (lean_is_scalar(x_395)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_395;
}
lean_ctor_set(x_397, 0, x_365);
lean_ctor_set(x_397, 1, x_366);
lean_ctor_set(x_397, 2, x_367);
lean_ctor_set(x_397, 3, x_378);
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_396);
if (lean_is_scalar(x_390)) {
 x_398 = lean_alloc_ctor(1, 4, 1);
} else {
 x_398 = x_390;
}
lean_ctor_set(x_398, 0, x_391);
lean_ctor_set(x_398, 1, x_392);
lean_ctor_set(x_398, 2, x_393);
lean_ctor_set(x_398, 3, x_394);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_396);
x_399 = 0;
x_400 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_388);
lean_ctor_set(x_400, 2, x_389);
lean_ctor_set(x_400, 3, x_398);
lean_ctor_set_uint8(x_400, sizeof(void*)*4, x_399);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; 
x_401 = lean_ctor_get(x_377, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_377, 2);
lean_inc(x_402);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_403 = x_377;
} else {
 lean_dec_ref(x_377);
 x_403 = lean_box(0);
}
x_404 = 0;
if (lean_is_scalar(x_403)) {
 x_405 = lean_alloc_ctor(1, 4, 1);
} else {
 x_405 = x_403;
}
lean_ctor_set(x_405, 0, x_378);
lean_ctor_set(x_405, 1, x_401);
lean_ctor_set(x_405, 2, x_402);
lean_ctor_set(x_405, 3, x_379);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_404);
x_406 = 1;
x_407 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_407, 0, x_365);
lean_ctor_set(x_407, 1, x_366);
lean_ctor_set(x_407, 2, x_367);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
return x_407;
}
}
}
else
{
uint8_t x_408; 
x_408 = lean_ctor_get_uint8(x_378, sizeof(void*)*4);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; 
x_409 = lean_ctor_get(x_377, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_377, 2);
lean_inc(x_410);
x_411 = lean_ctor_get(x_377, 3);
lean_inc(x_411);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_412 = x_377;
} else {
 lean_dec_ref(x_377);
 x_412 = lean_box(0);
}
x_413 = lean_ctor_get(x_378, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_378, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_378, 2);
lean_inc(x_415);
x_416 = lean_ctor_get(x_378, 3);
lean_inc(x_416);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_417 = x_378;
} else {
 lean_dec_ref(x_378);
 x_417 = lean_box(0);
}
x_418 = 1;
if (lean_is_scalar(x_417)) {
 x_419 = lean_alloc_ctor(1, 4, 1);
} else {
 x_419 = x_417;
}
lean_ctor_set(x_419, 0, x_365);
lean_ctor_set(x_419, 1, x_366);
lean_ctor_set(x_419, 2, x_367);
lean_ctor_set(x_419, 3, x_413);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
if (lean_is_scalar(x_412)) {
 x_420 = lean_alloc_ctor(1, 4, 1);
} else {
 x_420 = x_412;
}
lean_ctor_set(x_420, 0, x_416);
lean_ctor_set(x_420, 1, x_409);
lean_ctor_set(x_420, 2, x_410);
lean_ctor_set(x_420, 3, x_411);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_418);
x_421 = 0;
x_422 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_414);
lean_ctor_set(x_422, 2, x_415);
lean_ctor_set(x_422, 3, x_420);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
return x_422;
}
else
{
lean_object* x_423; 
x_423 = lean_ctor_get(x_377, 3);
lean_inc(x_423);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; 
x_424 = lean_ctor_get(x_377, 1);
lean_inc(x_424);
x_425 = lean_ctor_get(x_377, 2);
lean_inc(x_425);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_426 = x_377;
} else {
 lean_dec_ref(x_377);
 x_426 = lean_box(0);
}
x_427 = 0;
if (lean_is_scalar(x_426)) {
 x_428 = lean_alloc_ctor(1, 4, 1);
} else {
 x_428 = x_426;
}
lean_ctor_set(x_428, 0, x_378);
lean_ctor_set(x_428, 1, x_424);
lean_ctor_set(x_428, 2, x_425);
lean_ctor_set(x_428, 3, x_423);
lean_ctor_set_uint8(x_428, sizeof(void*)*4, x_427);
x_429 = 1;
x_430 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_430, 0, x_365);
lean_ctor_set(x_430, 1, x_366);
lean_ctor_set(x_430, 2, x_367);
lean_ctor_set(x_430, 3, x_428);
lean_ctor_set_uint8(x_430, sizeof(void*)*4, x_429);
return x_430;
}
else
{
uint8_t x_431; 
x_431 = lean_ctor_get_uint8(x_423, sizeof(void*)*4);
if (x_431 == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; 
x_432 = lean_ctor_get(x_377, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_377, 2);
lean_inc(x_433);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_434 = x_377;
} else {
 lean_dec_ref(x_377);
 x_434 = lean_box(0);
}
x_435 = lean_ctor_get(x_423, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_423, 1);
lean_inc(x_436);
x_437 = lean_ctor_get(x_423, 2);
lean_inc(x_437);
x_438 = lean_ctor_get(x_423, 3);
lean_inc(x_438);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 lean_ctor_release(x_423, 2);
 lean_ctor_release(x_423, 3);
 x_439 = x_423;
} else {
 lean_dec_ref(x_423);
 x_439 = lean_box(0);
}
x_440 = 1;
lean_inc(x_378);
if (lean_is_scalar(x_439)) {
 x_441 = lean_alloc_ctor(1, 4, 1);
} else {
 x_441 = x_439;
}
lean_ctor_set(x_441, 0, x_365);
lean_ctor_set(x_441, 1, x_366);
lean_ctor_set(x_441, 2, x_367);
lean_ctor_set(x_441, 3, x_378);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_442 = x_378;
} else {
 lean_dec_ref(x_378);
 x_442 = lean_box(0);
}
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_440);
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_435);
lean_ctor_set(x_443, 1, x_436);
lean_ctor_set(x_443, 2, x_437);
lean_ctor_set(x_443, 3, x_438);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_440);
x_444 = 0;
if (lean_is_scalar(x_434)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_434;
}
lean_ctor_set(x_445, 0, x_441);
lean_ctor_set(x_445, 1, x_432);
lean_ctor_set(x_445, 2, x_433);
lean_ctor_set(x_445, 3, x_443);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_444);
return x_445;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; uint8_t x_457; lean_object* x_458; 
x_446 = lean_ctor_get(x_377, 1);
lean_inc(x_446);
x_447 = lean_ctor_get(x_377, 2);
lean_inc(x_447);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_448 = x_377;
} else {
 lean_dec_ref(x_377);
 x_448 = lean_box(0);
}
x_449 = lean_ctor_get(x_378, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_378, 1);
lean_inc(x_450);
x_451 = lean_ctor_get(x_378, 2);
lean_inc(x_451);
x_452 = lean_ctor_get(x_378, 3);
lean_inc(x_452);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_453 = x_378;
} else {
 lean_dec_ref(x_378);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 4, 1);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_449);
lean_ctor_set(x_454, 1, x_450);
lean_ctor_set(x_454, 2, x_451);
lean_ctor_set(x_454, 3, x_452);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_431);
x_455 = 0;
if (lean_is_scalar(x_448)) {
 x_456 = lean_alloc_ctor(1, 4, 1);
} else {
 x_456 = x_448;
}
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_446);
lean_ctor_set(x_456, 2, x_447);
lean_ctor_set(x_456, 3, x_423);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_455);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_365);
lean_ctor_set(x_458, 1, x_366);
lean_ctor_set(x_458, 2, x_367);
lean_ctor_set(x_458, 3, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
}
}
}
}
}
}
else
{
uint8_t x_459; 
x_459 = l_Std_RBNode_isRed___rarg(x_365);
if (x_459 == 0)
{
lean_object* x_460; uint8_t x_461; lean_object* x_462; 
x_460 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_365, x_2, x_3);
x_461 = 1;
x_462 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_366);
lean_ctor_set(x_462, 2, x_367);
lean_ctor_set(x_462, 3, x_368);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
return x_462;
}
else
{
lean_object* x_463; lean_object* x_464; 
x_463 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_365, x_2, x_3);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; 
x_465 = lean_ctor_get(x_463, 3);
lean_inc(x_465);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; lean_object* x_470; uint8_t x_471; lean_object* x_472; 
x_466 = lean_ctor_get(x_463, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_463, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_468 = x_463;
} else {
 lean_dec_ref(x_463);
 x_468 = lean_box(0);
}
x_469 = 0;
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(1, 4, 1);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_465);
lean_ctor_set(x_470, 1, x_466);
lean_ctor_set(x_470, 2, x_467);
lean_ctor_set(x_470, 3, x_465);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_469);
x_471 = 1;
x_472 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_366);
lean_ctor_set(x_472, 2, x_367);
lean_ctor_set(x_472, 3, x_368);
lean_ctor_set_uint8(x_472, sizeof(void*)*4, x_471);
return x_472;
}
else
{
uint8_t x_473; 
x_473 = lean_ctor_get_uint8(x_465, sizeof(void*)*4);
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; 
x_474 = lean_ctor_get(x_463, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_463, 2);
lean_inc(x_475);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_476 = x_463;
} else {
 lean_dec_ref(x_463);
 x_476 = lean_box(0);
}
x_477 = lean_ctor_get(x_465, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_465, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_465, 2);
lean_inc(x_479);
x_480 = lean_ctor_get(x_465, 3);
lean_inc(x_480);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 lean_ctor_release(x_465, 2);
 lean_ctor_release(x_465, 3);
 x_481 = x_465;
} else {
 lean_dec_ref(x_465);
 x_481 = lean_box(0);
}
x_482 = 1;
if (lean_is_scalar(x_481)) {
 x_483 = lean_alloc_ctor(1, 4, 1);
} else {
 x_483 = x_481;
}
lean_ctor_set(x_483, 0, x_464);
lean_ctor_set(x_483, 1, x_474);
lean_ctor_set(x_483, 2, x_475);
lean_ctor_set(x_483, 3, x_477);
lean_ctor_set_uint8(x_483, sizeof(void*)*4, x_482);
if (lean_is_scalar(x_476)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_476;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_366);
lean_ctor_set(x_484, 2, x_367);
lean_ctor_set(x_484, 3, x_368);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_482);
x_485 = 0;
x_486 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_478);
lean_ctor_set(x_486, 2, x_479);
lean_ctor_set(x_486, 3, x_484);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_485);
return x_486;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; lean_object* x_491; uint8_t x_492; lean_object* x_493; 
x_487 = lean_ctor_get(x_463, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_463, 2);
lean_inc(x_488);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_489 = x_463;
} else {
 lean_dec_ref(x_463);
 x_489 = lean_box(0);
}
x_490 = 0;
if (lean_is_scalar(x_489)) {
 x_491 = lean_alloc_ctor(1, 4, 1);
} else {
 x_491 = x_489;
}
lean_ctor_set(x_491, 0, x_464);
lean_ctor_set(x_491, 1, x_487);
lean_ctor_set(x_491, 2, x_488);
lean_ctor_set(x_491, 3, x_465);
lean_ctor_set_uint8(x_491, sizeof(void*)*4, x_490);
x_492 = 1;
x_493 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_366);
lean_ctor_set(x_493, 2, x_367);
lean_ctor_set(x_493, 3, x_368);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_492);
return x_493;
}
}
}
else
{
uint8_t x_494; 
x_494 = lean_ctor_get_uint8(x_464, sizeof(void*)*4);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; lean_object* x_508; 
x_495 = lean_ctor_get(x_463, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_463, 2);
lean_inc(x_496);
x_497 = lean_ctor_get(x_463, 3);
lean_inc(x_497);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_498 = x_463;
} else {
 lean_dec_ref(x_463);
 x_498 = lean_box(0);
}
x_499 = lean_ctor_get(x_464, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_464, 1);
lean_inc(x_500);
x_501 = lean_ctor_get(x_464, 2);
lean_inc(x_501);
x_502 = lean_ctor_get(x_464, 3);
lean_inc(x_502);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_503 = x_464;
} else {
 lean_dec_ref(x_464);
 x_503 = lean_box(0);
}
x_504 = 1;
if (lean_is_scalar(x_503)) {
 x_505 = lean_alloc_ctor(1, 4, 1);
} else {
 x_505 = x_503;
}
lean_ctor_set(x_505, 0, x_499);
lean_ctor_set(x_505, 1, x_500);
lean_ctor_set(x_505, 2, x_501);
lean_ctor_set(x_505, 3, x_502);
lean_ctor_set_uint8(x_505, sizeof(void*)*4, x_504);
if (lean_is_scalar(x_498)) {
 x_506 = lean_alloc_ctor(1, 4, 1);
} else {
 x_506 = x_498;
}
lean_ctor_set(x_506, 0, x_497);
lean_ctor_set(x_506, 1, x_366);
lean_ctor_set(x_506, 2, x_367);
lean_ctor_set(x_506, 3, x_368);
lean_ctor_set_uint8(x_506, sizeof(void*)*4, x_504);
x_507 = 0;
x_508 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_495);
lean_ctor_set(x_508, 2, x_496);
lean_ctor_set(x_508, 3, x_506);
lean_ctor_set_uint8(x_508, sizeof(void*)*4, x_507);
return x_508;
}
else
{
lean_object* x_509; 
x_509 = lean_ctor_get(x_463, 3);
lean_inc(x_509);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; lean_object* x_514; uint8_t x_515; lean_object* x_516; 
x_510 = lean_ctor_get(x_463, 1);
lean_inc(x_510);
x_511 = lean_ctor_get(x_463, 2);
lean_inc(x_511);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_512 = x_463;
} else {
 lean_dec_ref(x_463);
 x_512 = lean_box(0);
}
x_513 = 0;
if (lean_is_scalar(x_512)) {
 x_514 = lean_alloc_ctor(1, 4, 1);
} else {
 x_514 = x_512;
}
lean_ctor_set(x_514, 0, x_464);
lean_ctor_set(x_514, 1, x_510);
lean_ctor_set(x_514, 2, x_511);
lean_ctor_set(x_514, 3, x_509);
lean_ctor_set_uint8(x_514, sizeof(void*)*4, x_513);
x_515 = 1;
x_516 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_366);
lean_ctor_set(x_516, 2, x_367);
lean_ctor_set(x_516, 3, x_368);
lean_ctor_set_uint8(x_516, sizeof(void*)*4, x_515);
return x_516;
}
else
{
uint8_t x_517; 
x_517 = lean_ctor_get_uint8(x_509, sizeof(void*)*4);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; uint8_t x_530; lean_object* x_531; 
x_518 = lean_ctor_get(x_463, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_463, 2);
lean_inc(x_519);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_520 = x_463;
} else {
 lean_dec_ref(x_463);
 x_520 = lean_box(0);
}
x_521 = lean_ctor_get(x_509, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_509, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_509, 2);
lean_inc(x_523);
x_524 = lean_ctor_get(x_509, 3);
lean_inc(x_524);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 lean_ctor_release(x_509, 2);
 lean_ctor_release(x_509, 3);
 x_525 = x_509;
} else {
 lean_dec_ref(x_509);
 x_525 = lean_box(0);
}
x_526 = 1;
lean_inc(x_464);
if (lean_is_scalar(x_525)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_525;
}
lean_ctor_set(x_527, 0, x_464);
lean_ctor_set(x_527, 1, x_518);
lean_ctor_set(x_527, 2, x_519);
lean_ctor_set(x_527, 3, x_521);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_528 = x_464;
} else {
 lean_dec_ref(x_464);
 x_528 = lean_box(0);
}
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(1, 4, 1);
} else {
 x_529 = x_528;
}
lean_ctor_set(x_529, 0, x_524);
lean_ctor_set(x_529, 1, x_366);
lean_ctor_set(x_529, 2, x_367);
lean_ctor_set(x_529, 3, x_368);
lean_ctor_set_uint8(x_529, sizeof(void*)*4, x_526);
x_530 = 0;
if (lean_is_scalar(x_520)) {
 x_531 = lean_alloc_ctor(1, 4, 1);
} else {
 x_531 = x_520;
}
lean_ctor_set(x_531, 0, x_527);
lean_ctor_set(x_531, 1, x_522);
lean_ctor_set(x_531, 2, x_523);
lean_ctor_set(x_531, 3, x_529);
lean_ctor_set_uint8(x_531, sizeof(void*)*4, x_530);
return x_531;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; uint8_t x_543; lean_object* x_544; 
x_532 = lean_ctor_get(x_463, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_463, 2);
lean_inc(x_533);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_534 = x_463;
} else {
 lean_dec_ref(x_463);
 x_534 = lean_box(0);
}
x_535 = lean_ctor_get(x_464, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_464, 1);
lean_inc(x_536);
x_537 = lean_ctor_get(x_464, 2);
lean_inc(x_537);
x_538 = lean_ctor_get(x_464, 3);
lean_inc(x_538);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_539 = x_464;
} else {
 lean_dec_ref(x_464);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 4, 1);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_535);
lean_ctor_set(x_540, 1, x_536);
lean_ctor_set(x_540, 2, x_537);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_517);
x_541 = 0;
if (lean_is_scalar(x_534)) {
 x_542 = lean_alloc_ctor(1, 4, 1);
} else {
 x_542 = x_534;
}
lean_ctor_set(x_542, 0, x_540);
lean_ctor_set(x_542, 1, x_532);
lean_ctor_set(x_542, 2, x_533);
lean_ctor_set(x_542, 3, x_509);
lean_ctor_set_uint8(x_542, sizeof(void*)*4, x_541);
x_543 = 1;
x_544 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_366);
lean_ctor_set(x_544, 2, x_367);
lean_ctor_set(x_544, 3, x_368);
lean_ctor_set_uint8(x_544, sizeof(void*)*4, x_543);
return x_544;
}
}
}
}
}
}
}
}
}
}
}
lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_1, x_2, x_3);
x_7 = l_Std_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
lean_object* l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = l_Lean_Name_quickLt(x_2, x_10);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Name_quickLt(x_10, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_10);
x_15 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_12, x_2, x_3);
x_17 = 0;
lean_ctor_set(x_1, 3, x_16);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_17);
return x_1;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_9, x_2, x_3);
x_19 = 0;
lean_ctor_set(x_1, 0, x_18);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = l_Lean_Name_quickLt(x_2, x_21);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Name_quickLt(x_21, x_2);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_21);
x_26 = 0;
x_27 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set(x_27, 2, x_3);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_26);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_23, x_2, x_3);
x_29 = 0;
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_22);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_29);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_20, x_2, x_3);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = l_Lean_Name_quickLt(x_2, x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Name_quickLt(x_36, x_2);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_37);
lean_dec(x_36);
x_41 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_41);
return x_1;
}
else
{
uint8_t x_42; 
x_42 = l_Std_RBNode_isRed___rarg(x_38);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_38, x_2, x_3);
x_44 = 1;
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_44);
return x_1;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_38, x_2, x_3);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 3);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_45, 3);
lean_dec(x_49);
x_50 = lean_ctor_get(x_45, 0);
lean_dec(x_50);
x_51 = 0;
lean_ctor_set(x_45, 0, x_47);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_51);
x_52 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_52);
return x_1;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_45, 1);
x_54 = lean_ctor_get(x_45, 2);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_45);
x_55 = 0;
x_56 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_56, 2, x_54);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_55);
x_57 = 1;
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_57);
return x_1;
}
}
else
{
uint8_t x_58; 
x_58 = lean_ctor_get_uint8(x_47, sizeof(void*)*4);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_45);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_45, 1);
x_61 = lean_ctor_get(x_45, 2);
x_62 = lean_ctor_get(x_45, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_45, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_47);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_47, 0);
x_66 = lean_ctor_get(x_47, 1);
x_67 = lean_ctor_get(x_47, 2);
x_68 = lean_ctor_get(x_47, 3);
x_69 = 1;
lean_ctor_set(x_47, 3, x_46);
lean_ctor_set(x_47, 2, x_37);
lean_ctor_set(x_47, 1, x_36);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_69);
lean_ctor_set(x_45, 3, x_68);
lean_ctor_set(x_45, 2, x_67);
lean_ctor_set(x_45, 1, x_66);
lean_ctor_set(x_45, 0, x_65);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_69);
x_70 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_61);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_1, 0, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_70);
return x_1;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; 
x_71 = lean_ctor_get(x_47, 0);
x_72 = lean_ctor_get(x_47, 1);
x_73 = lean_ctor_get(x_47, 2);
x_74 = lean_ctor_get(x_47, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_47);
x_75 = 1;
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_35);
lean_ctor_set(x_76, 1, x_36);
lean_ctor_set(x_76, 2, x_37);
lean_ctor_set(x_76, 3, x_46);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_75);
lean_ctor_set(x_45, 3, x_74);
lean_ctor_set(x_45, 2, x_73);
lean_ctor_set(x_45, 1, x_72);
lean_ctor_set(x_45, 0, x_71);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_75);
x_77 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_61);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_1, 0, x_76);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_77);
return x_1;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_78 = lean_ctor_get(x_45, 1);
x_79 = lean_ctor_get(x_45, 2);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_45);
x_80 = lean_ctor_get(x_47, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_47, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_47, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_47, 3);
lean_inc(x_83);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_84 = x_47;
} else {
 lean_dec_ref(x_47);
 x_84 = lean_box(0);
}
x_85 = 1;
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(1, 4, 1);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_35);
lean_ctor_set(x_86, 1, x_36);
lean_ctor_set(x_86, 2, x_37);
lean_ctor_set(x_86, 3, x_46);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_85);
x_87 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_81);
lean_ctor_set(x_87, 2, x_82);
lean_ctor_set(x_87, 3, x_83);
lean_ctor_set_uint8(x_87, sizeof(void*)*4, x_85);
x_88 = 0;
lean_ctor_set(x_1, 3, x_87);
lean_ctor_set(x_1, 2, x_79);
lean_ctor_set(x_1, 1, x_78);
lean_ctor_set(x_1, 0, x_86);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_88);
return x_1;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_45);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_45, 3);
lean_dec(x_90);
x_91 = lean_ctor_get(x_45, 0);
lean_dec(x_91);
x_92 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_92);
x_93 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_93);
return x_1;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_45, 1);
x_95 = lean_ctor_get(x_45, 2);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_45);
x_96 = 0;
x_97 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_97, 0, x_46);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_47);
lean_ctor_set_uint8(x_97, sizeof(void*)*4, x_96);
x_98 = 1;
lean_ctor_set(x_1, 3, x_97);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_98);
return x_1;
}
}
}
}
else
{
uint8_t x_99; 
x_99 = lean_ctor_get_uint8(x_46, sizeof(void*)*4);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_45);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_45, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_46);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; 
x_103 = lean_ctor_get(x_46, 0);
x_104 = lean_ctor_get(x_46, 1);
x_105 = lean_ctor_get(x_46, 2);
x_106 = lean_ctor_get(x_46, 3);
x_107 = 1;
lean_ctor_set(x_46, 3, x_103);
lean_ctor_set(x_46, 2, x_37);
lean_ctor_set(x_46, 1, x_36);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_107);
lean_ctor_set(x_45, 0, x_106);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_107);
x_108 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_105);
lean_ctor_set(x_1, 1, x_104);
lean_ctor_set(x_1, 0, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_108);
return x_1;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; uint8_t x_115; 
x_109 = lean_ctor_get(x_46, 0);
x_110 = lean_ctor_get(x_46, 1);
x_111 = lean_ctor_get(x_46, 2);
x_112 = lean_ctor_get(x_46, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_46);
x_113 = 1;
x_114 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_114, 0, x_35);
lean_ctor_set(x_114, 1, x_36);
lean_ctor_set(x_114, 2, x_37);
lean_ctor_set(x_114, 3, x_109);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_113);
lean_ctor_set(x_45, 0, x_112);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_113);
x_115 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_111);
lean_ctor_set(x_1, 1, x_110);
lean_ctor_set(x_1, 0, x_114);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_115);
return x_1;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_116 = lean_ctor_get(x_45, 1);
x_117 = lean_ctor_get(x_45, 2);
x_118 = lean_ctor_get(x_45, 3);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_45);
x_119 = lean_ctor_get(x_46, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_46, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_46, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_46, 3);
lean_inc(x_122);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_123 = x_46;
} else {
 lean_dec_ref(x_46);
 x_123 = lean_box(0);
}
x_124 = 1;
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(1, 4, 1);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_35);
lean_ctor_set(x_125, 1, x_36);
lean_ctor_set(x_125, 2, x_37);
lean_ctor_set(x_125, 3, x_119);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_124);
x_126 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_116);
lean_ctor_set(x_126, 2, x_117);
lean_ctor_set(x_126, 3, x_118);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_124);
x_127 = 0;
lean_ctor_set(x_1, 3, x_126);
lean_ctor_set(x_1, 2, x_121);
lean_ctor_set(x_1, 1, x_120);
lean_ctor_set(x_1, 0, x_125);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_127);
return x_1;
}
}
else
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_45, 3);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_45);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_45, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_45, 0);
lean_dec(x_131);
x_132 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_132);
x_133 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_133);
return x_1;
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; uint8_t x_138; 
x_134 = lean_ctor_get(x_45, 1);
x_135 = lean_ctor_get(x_45, 2);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_45);
x_136 = 0;
x_137 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_137, 0, x_46);
lean_ctor_set(x_137, 1, x_134);
lean_ctor_set(x_137, 2, x_135);
lean_ctor_set(x_137, 3, x_128);
lean_ctor_set_uint8(x_137, sizeof(void*)*4, x_136);
x_138 = 1;
lean_ctor_set(x_1, 3, x_137);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_138);
return x_1;
}
}
else
{
uint8_t x_139; 
x_139 = lean_ctor_get_uint8(x_128, sizeof(void*)*4);
if (x_139 == 0)
{
uint8_t x_140; 
lean_free_object(x_1);
x_140 = !lean_is_exclusive(x_45);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_45, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_45, 0);
lean_dec(x_142);
x_143 = !lean_is_exclusive(x_128);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; 
x_144 = lean_ctor_get(x_128, 0);
x_145 = lean_ctor_get(x_128, 1);
x_146 = lean_ctor_get(x_128, 2);
x_147 = lean_ctor_get(x_128, 3);
x_148 = 1;
lean_inc(x_46);
lean_ctor_set(x_128, 3, x_46);
lean_ctor_set(x_128, 2, x_37);
lean_ctor_set(x_128, 1, x_36);
lean_ctor_set(x_128, 0, x_35);
x_149 = !lean_is_exclusive(x_46);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_150 = lean_ctor_get(x_46, 3);
lean_dec(x_150);
x_151 = lean_ctor_get(x_46, 2);
lean_dec(x_151);
x_152 = lean_ctor_get(x_46, 1);
lean_dec(x_152);
x_153 = lean_ctor_get(x_46, 0);
lean_dec(x_153);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_148);
lean_ctor_set(x_46, 3, x_147);
lean_ctor_set(x_46, 2, x_146);
lean_ctor_set(x_46, 1, x_145);
lean_ctor_set(x_46, 0, x_144);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_148);
x_154 = 0;
lean_ctor_set(x_45, 3, x_46);
lean_ctor_set(x_45, 0, x_128);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_154);
return x_45;
}
else
{
lean_object* x_155; uint8_t x_156; 
lean_dec(x_46);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_148);
x_155 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_155, 0, x_144);
lean_ctor_set(x_155, 1, x_145);
lean_ctor_set(x_155, 2, x_146);
lean_ctor_set(x_155, 3, x_147);
lean_ctor_set_uint8(x_155, sizeof(void*)*4, x_148);
x_156 = 0;
lean_ctor_set(x_45, 3, x_155);
lean_ctor_set(x_45, 0, x_128);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_156);
return x_45;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_157 = lean_ctor_get(x_128, 0);
x_158 = lean_ctor_get(x_128, 1);
x_159 = lean_ctor_get(x_128, 2);
x_160 = lean_ctor_get(x_128, 3);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_128);
x_161 = 1;
lean_inc(x_46);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_35);
lean_ctor_set(x_162, 1, x_36);
lean_ctor_set(x_162, 2, x_37);
lean_ctor_set(x_162, 3, x_46);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_163 = x_46;
} else {
 lean_dec_ref(x_46);
 x_163 = lean_box(0);
}
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_161);
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 4, 1);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_157);
lean_ctor_set(x_164, 1, x_158);
lean_ctor_set(x_164, 2, x_159);
lean_ctor_set(x_164, 3, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_161);
x_165 = 0;
lean_ctor_set(x_45, 3, x_164);
lean_ctor_set(x_45, 0, x_162);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_165);
return x_45;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; 
x_166 = lean_ctor_get(x_45, 1);
x_167 = lean_ctor_get(x_45, 2);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_45);
x_168 = lean_ctor_get(x_128, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_128, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_128, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_128, 3);
lean_inc(x_171);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 x_172 = x_128;
} else {
 lean_dec_ref(x_128);
 x_172 = lean_box(0);
}
x_173 = 1;
lean_inc(x_46);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(1, 4, 1);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_35);
lean_ctor_set(x_174, 1, x_36);
lean_ctor_set(x_174, 2, x_37);
lean_ctor_set(x_174, 3, x_46);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_175 = x_46;
} else {
 lean_dec_ref(x_46);
 x_175 = lean_box(0);
}
lean_ctor_set_uint8(x_174, sizeof(void*)*4, x_173);
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 4, 1);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_168);
lean_ctor_set(x_176, 1, x_169);
lean_ctor_set(x_176, 2, x_170);
lean_ctor_set(x_176, 3, x_171);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_173);
x_177 = 0;
x_178 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_166);
lean_ctor_set(x_178, 2, x_167);
lean_ctor_set(x_178, 3, x_176);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_177);
return x_178;
}
}
else
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_45);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_45, 3);
lean_dec(x_180);
x_181 = lean_ctor_get(x_45, 0);
lean_dec(x_181);
x_182 = !lean_is_exclusive(x_46);
if (x_182 == 0)
{
uint8_t x_183; uint8_t x_184; 
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_139);
x_183 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_183);
x_184 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_184);
return x_1;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_191; 
x_185 = lean_ctor_get(x_46, 0);
x_186 = lean_ctor_get(x_46, 1);
x_187 = lean_ctor_get(x_46, 2);
x_188 = lean_ctor_get(x_46, 3);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_46);
x_189 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_189, 0, x_185);
lean_ctor_set(x_189, 1, x_186);
lean_ctor_set(x_189, 2, x_187);
lean_ctor_set(x_189, 3, x_188);
lean_ctor_set_uint8(x_189, sizeof(void*)*4, x_139);
x_190 = 0;
lean_ctor_set(x_45, 0, x_189);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_190);
x_191 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_191);
return x_1;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; uint8_t x_202; 
x_192 = lean_ctor_get(x_45, 1);
x_193 = lean_ctor_get(x_45, 2);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_45);
x_194 = lean_ctor_get(x_46, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_46, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_46, 2);
lean_inc(x_196);
x_197 = lean_ctor_get(x_46, 3);
lean_inc(x_197);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_198 = x_46;
} else {
 lean_dec_ref(x_46);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 4, 1);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_194);
lean_ctor_set(x_199, 1, x_195);
lean_ctor_set(x_199, 2, x_196);
lean_ctor_set(x_199, 3, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_139);
x_200 = 0;
x_201 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_192);
lean_ctor_set(x_201, 2, x_193);
lean_ctor_set(x_201, 3, x_128);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_200);
x_202 = 1;
lean_ctor_set(x_1, 3, x_201);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
}
}
}
}
}
}
}
}
else
{
uint8_t x_203; 
x_203 = l_Std_RBNode_isRed___rarg(x_35);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_35, x_2, x_3);
x_205 = 1;
lean_ctor_set(x_1, 0, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_205);
return x_1;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_35, x_2, x_3);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_206, 3);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_206);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; uint8_t x_213; 
x_210 = lean_ctor_get(x_206, 3);
lean_dec(x_210);
x_211 = lean_ctor_get(x_206, 0);
lean_dec(x_211);
x_212 = 0;
lean_ctor_set(x_206, 0, x_208);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_212);
x_213 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_213);
return x_1;
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_206, 1);
x_215 = lean_ctor_get(x_206, 2);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_206);
x_216 = 0;
x_217 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_217, 0, x_208);
lean_ctor_set(x_217, 1, x_214);
lean_ctor_set(x_217, 2, x_215);
lean_ctor_set(x_217, 3, x_208);
lean_ctor_set_uint8(x_217, sizeof(void*)*4, x_216);
x_218 = 1;
lean_ctor_set(x_1, 0, x_217);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_218);
return x_1;
}
}
else
{
uint8_t x_219; 
x_219 = lean_ctor_get_uint8(x_208, sizeof(void*)*4);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_206);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_221 = lean_ctor_get(x_206, 1);
x_222 = lean_ctor_get(x_206, 2);
x_223 = lean_ctor_get(x_206, 3);
lean_dec(x_223);
x_224 = lean_ctor_get(x_206, 0);
lean_dec(x_224);
x_225 = !lean_is_exclusive(x_208);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_231; 
x_226 = lean_ctor_get(x_208, 0);
x_227 = lean_ctor_get(x_208, 1);
x_228 = lean_ctor_get(x_208, 2);
x_229 = lean_ctor_get(x_208, 3);
x_230 = 1;
lean_ctor_set(x_208, 3, x_226);
lean_ctor_set(x_208, 2, x_222);
lean_ctor_set(x_208, 1, x_221);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_230);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_229);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_230);
x_231 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_208);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_231);
return x_1;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; uint8_t x_238; 
x_232 = lean_ctor_get(x_208, 0);
x_233 = lean_ctor_get(x_208, 1);
x_234 = lean_ctor_get(x_208, 2);
x_235 = lean_ctor_get(x_208, 3);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_208);
x_236 = 1;
x_237 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_237, 0, x_207);
lean_ctor_set(x_237, 1, x_221);
lean_ctor_set(x_237, 2, x_222);
lean_ctor_set(x_237, 3, x_232);
lean_ctor_set_uint8(x_237, sizeof(void*)*4, x_236);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_235);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_236);
x_238 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_234);
lean_ctor_set(x_1, 1, x_233);
lean_ctor_set(x_1, 0, x_237);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_238);
return x_1;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_239 = lean_ctor_get(x_206, 1);
x_240 = lean_ctor_get(x_206, 2);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_206);
x_241 = lean_ctor_get(x_208, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_208, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_208, 2);
lean_inc(x_243);
x_244 = lean_ctor_get(x_208, 3);
lean_inc(x_244);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 lean_ctor_release(x_208, 3);
 x_245 = x_208;
} else {
 lean_dec_ref(x_208);
 x_245 = lean_box(0);
}
x_246 = 1;
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(1, 4, 1);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_207);
lean_ctor_set(x_247, 1, x_239);
lean_ctor_set(x_247, 2, x_240);
lean_ctor_set(x_247, 3, x_241);
lean_ctor_set_uint8(x_247, sizeof(void*)*4, x_246);
x_248 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_248, 0, x_244);
lean_ctor_set(x_248, 1, x_36);
lean_ctor_set(x_248, 2, x_37);
lean_ctor_set(x_248, 3, x_38);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_246);
x_249 = 0;
lean_ctor_set(x_1, 3, x_248);
lean_ctor_set(x_1, 2, x_243);
lean_ctor_set(x_1, 1, x_242);
lean_ctor_set(x_1, 0, x_247);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_249);
return x_1;
}
}
else
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_206);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_254; 
x_251 = lean_ctor_get(x_206, 3);
lean_dec(x_251);
x_252 = lean_ctor_get(x_206, 0);
lean_dec(x_252);
x_253 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_253);
x_254 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_254);
return x_1;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_255 = lean_ctor_get(x_206, 1);
x_256 = lean_ctor_get(x_206, 2);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_206);
x_257 = 0;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_207);
lean_ctor_set(x_258, 1, x_255);
lean_ctor_set(x_258, 2, x_256);
lean_ctor_set(x_258, 3, x_208);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
x_259 = 1;
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
else
{
uint8_t x_260; 
x_260 = lean_ctor_get_uint8(x_207, sizeof(void*)*4);
if (x_260 == 0)
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_206);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_262 = lean_ctor_get(x_206, 1);
x_263 = lean_ctor_get(x_206, 2);
x_264 = lean_ctor_get(x_206, 3);
x_265 = lean_ctor_get(x_206, 0);
lean_dec(x_265);
x_266 = !lean_is_exclusive(x_207);
if (x_266 == 0)
{
uint8_t x_267; uint8_t x_268; 
x_267 = 1;
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_267);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_267);
x_268 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_207);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_268);
return x_1;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; uint8_t x_275; 
x_269 = lean_ctor_get(x_207, 0);
x_270 = lean_ctor_get(x_207, 1);
x_271 = lean_ctor_get(x_207, 2);
x_272 = lean_ctor_get(x_207, 3);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_207);
x_273 = 1;
x_274 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_274, 0, x_269);
lean_ctor_set(x_274, 1, x_270);
lean_ctor_set(x_274, 2, x_271);
lean_ctor_set(x_274, 3, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*4, x_273);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_273);
x_275 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_274);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_275);
return x_1;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_276 = lean_ctor_get(x_206, 1);
x_277 = lean_ctor_get(x_206, 2);
x_278 = lean_ctor_get(x_206, 3);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_206);
x_279 = lean_ctor_get(x_207, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_207, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_207, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_207, 3);
lean_inc(x_282);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_283 = x_207;
} else {
 lean_dec_ref(x_207);
 x_283 = lean_box(0);
}
x_284 = 1;
if (lean_is_scalar(x_283)) {
 x_285 = lean_alloc_ctor(1, 4, 1);
} else {
 x_285 = x_283;
}
lean_ctor_set(x_285, 0, x_279);
lean_ctor_set(x_285, 1, x_280);
lean_ctor_set(x_285, 2, x_281);
lean_ctor_set(x_285, 3, x_282);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_284);
x_286 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_286, 0, x_278);
lean_ctor_set(x_286, 1, x_36);
lean_ctor_set(x_286, 2, x_37);
lean_ctor_set(x_286, 3, x_38);
lean_ctor_set_uint8(x_286, sizeof(void*)*4, x_284);
x_287 = 0;
lean_ctor_set(x_1, 3, x_286);
lean_ctor_set(x_1, 2, x_277);
lean_ctor_set(x_1, 1, x_276);
lean_ctor_set(x_1, 0, x_285);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_287);
return x_1;
}
}
else
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_206, 3);
lean_inc(x_288);
if (lean_obj_tag(x_288) == 0)
{
uint8_t x_289; 
x_289 = !lean_is_exclusive(x_206);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_293; 
x_290 = lean_ctor_get(x_206, 3);
lean_dec(x_290);
x_291 = lean_ctor_get(x_206, 0);
lean_dec(x_291);
x_292 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_292);
x_293 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_293);
return x_1;
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_206, 1);
x_295 = lean_ctor_get(x_206, 2);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_206);
x_296 = 0;
x_297 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_297, 0, x_207);
lean_ctor_set(x_297, 1, x_294);
lean_ctor_set(x_297, 2, x_295);
lean_ctor_set(x_297, 3, x_288);
lean_ctor_set_uint8(x_297, sizeof(void*)*4, x_296);
x_298 = 1;
lean_ctor_set(x_1, 0, x_297);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_298);
return x_1;
}
}
else
{
uint8_t x_299; 
x_299 = lean_ctor_get_uint8(x_288, sizeof(void*)*4);
if (x_299 == 0)
{
uint8_t x_300; 
lean_free_object(x_1);
x_300 = !lean_is_exclusive(x_206);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_301 = lean_ctor_get(x_206, 1);
x_302 = lean_ctor_get(x_206, 2);
x_303 = lean_ctor_get(x_206, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_206, 0);
lean_dec(x_304);
x_305 = !lean_is_exclusive(x_288);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_311; 
x_306 = lean_ctor_get(x_288, 0);
x_307 = lean_ctor_get(x_288, 1);
x_308 = lean_ctor_get(x_288, 2);
x_309 = lean_ctor_get(x_288, 3);
x_310 = 1;
lean_inc(x_207);
lean_ctor_set(x_288, 3, x_306);
lean_ctor_set(x_288, 2, x_302);
lean_ctor_set(x_288, 1, x_301);
lean_ctor_set(x_288, 0, x_207);
x_311 = !lean_is_exclusive(x_207);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_312 = lean_ctor_get(x_207, 3);
lean_dec(x_312);
x_313 = lean_ctor_get(x_207, 2);
lean_dec(x_313);
x_314 = lean_ctor_get(x_207, 1);
lean_dec(x_314);
x_315 = lean_ctor_get(x_207, 0);
lean_dec(x_315);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
lean_ctor_set(x_207, 3, x_38);
lean_ctor_set(x_207, 2, x_37);
lean_ctor_set(x_207, 1, x_36);
lean_ctor_set(x_207, 0, x_309);
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_310);
x_316 = 0;
lean_ctor_set(x_206, 3, x_207);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_316);
return x_206;
}
else
{
lean_object* x_317; uint8_t x_318; 
lean_dec(x_207);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
x_317 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_36);
lean_ctor_set(x_317, 2, x_37);
lean_ctor_set(x_317, 3, x_38);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_310);
x_318 = 0;
lean_ctor_set(x_206, 3, x_317);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_318);
return x_206;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_319 = lean_ctor_get(x_288, 0);
x_320 = lean_ctor_get(x_288, 1);
x_321 = lean_ctor_get(x_288, 2);
x_322 = lean_ctor_get(x_288, 3);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_288);
x_323 = 1;
lean_inc(x_207);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_207);
lean_ctor_set(x_324, 1, x_301);
lean_ctor_set(x_324, 2, x_302);
lean_ctor_set(x_324, 3, x_319);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_325 = x_207;
} else {
 lean_dec_ref(x_207);
 x_325 = lean_box(0);
}
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_323);
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 4, 1);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_322);
lean_ctor_set(x_326, 1, x_36);
lean_ctor_set(x_326, 2, x_37);
lean_ctor_set(x_326, 3, x_38);
lean_ctor_set_uint8(x_326, sizeof(void*)*4, x_323);
x_327 = 0;
lean_ctor_set(x_206, 3, x_326);
lean_ctor_set(x_206, 2, x_321);
lean_ctor_set(x_206, 1, x_320);
lean_ctor_set(x_206, 0, x_324);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_327);
return x_206;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; 
x_328 = lean_ctor_get(x_206, 1);
x_329 = lean_ctor_get(x_206, 2);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_206);
x_330 = lean_ctor_get(x_288, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_288, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_288, 2);
lean_inc(x_332);
x_333 = lean_ctor_get(x_288, 3);
lean_inc(x_333);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 lean_ctor_release(x_288, 2);
 lean_ctor_release(x_288, 3);
 x_334 = x_288;
} else {
 lean_dec_ref(x_288);
 x_334 = lean_box(0);
}
x_335 = 1;
lean_inc(x_207);
if (lean_is_scalar(x_334)) {
 x_336 = lean_alloc_ctor(1, 4, 1);
} else {
 x_336 = x_334;
}
lean_ctor_set(x_336, 0, x_207);
lean_ctor_set(x_336, 1, x_328);
lean_ctor_set(x_336, 2, x_329);
lean_ctor_set(x_336, 3, x_330);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_337 = x_207;
} else {
 lean_dec_ref(x_207);
 x_337 = lean_box(0);
}
lean_ctor_set_uint8(x_336, sizeof(void*)*4, x_335);
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_36);
lean_ctor_set(x_338, 2, x_37);
lean_ctor_set(x_338, 3, x_38);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_335);
x_339 = 0;
x_340 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_340, 0, x_336);
lean_ctor_set(x_340, 1, x_331);
lean_ctor_set(x_340, 2, x_332);
lean_ctor_set(x_340, 3, x_338);
lean_ctor_set_uint8(x_340, sizeof(void*)*4, x_339);
return x_340;
}
}
else
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_206);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_342 = lean_ctor_get(x_206, 3);
lean_dec(x_342);
x_343 = lean_ctor_get(x_206, 0);
lean_dec(x_343);
x_344 = !lean_is_exclusive(x_207);
if (x_344 == 0)
{
uint8_t x_345; uint8_t x_346; 
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_299);
x_345 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_345);
x_346 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_346);
return x_1;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; uint8_t x_353; 
x_347 = lean_ctor_get(x_207, 0);
x_348 = lean_ctor_get(x_207, 1);
x_349 = lean_ctor_get(x_207, 2);
x_350 = lean_ctor_get(x_207, 3);
lean_inc(x_350);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_207);
x_351 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_351, 0, x_347);
lean_ctor_set(x_351, 1, x_348);
lean_ctor_set(x_351, 2, x_349);
lean_ctor_set(x_351, 3, x_350);
lean_ctor_set_uint8(x_351, sizeof(void*)*4, x_299);
x_352 = 0;
lean_ctor_set(x_206, 0, x_351);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_352);
x_353 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_353);
return x_1;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; uint8_t x_364; 
x_354 = lean_ctor_get(x_206, 1);
x_355 = lean_ctor_get(x_206, 2);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_206);
x_356 = lean_ctor_get(x_207, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_207, 1);
lean_inc(x_357);
x_358 = lean_ctor_get(x_207, 2);
lean_inc(x_358);
x_359 = lean_ctor_get(x_207, 3);
lean_inc(x_359);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_360 = x_207;
} else {
 lean_dec_ref(x_207);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 4, 1);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_356);
lean_ctor_set(x_361, 1, x_357);
lean_ctor_set(x_361, 2, x_358);
lean_ctor_set(x_361, 3, x_359);
lean_ctor_set_uint8(x_361, sizeof(void*)*4, x_299);
x_362 = 0;
x_363 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_354);
lean_ctor_set(x_363, 2, x_355);
lean_ctor_set(x_363, 3, x_288);
lean_ctor_set_uint8(x_363, sizeof(void*)*4, x_362);
x_364 = 1;
lean_ctor_set(x_1, 0, x_363);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_364);
return x_1;
}
}
}
}
}
}
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_365 = lean_ctor_get(x_1, 0);
x_366 = lean_ctor_get(x_1, 1);
x_367 = lean_ctor_get(x_1, 2);
x_368 = lean_ctor_get(x_1, 3);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_1);
x_369 = l_Lean_Name_quickLt(x_2, x_366);
if (x_369 == 0)
{
uint8_t x_370; 
x_370 = l_Lean_Name_quickLt(x_366, x_2);
if (x_370 == 0)
{
uint8_t x_371; lean_object* x_372; 
lean_dec(x_367);
lean_dec(x_366);
x_371 = 1;
x_372 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_372, 0, x_365);
lean_ctor_set(x_372, 1, x_2);
lean_ctor_set(x_372, 2, x_3);
lean_ctor_set(x_372, 3, x_368);
lean_ctor_set_uint8(x_372, sizeof(void*)*4, x_371);
return x_372;
}
else
{
uint8_t x_373; 
x_373 = l_Std_RBNode_isRed___rarg(x_368);
if (x_373 == 0)
{
lean_object* x_374; uint8_t x_375; lean_object* x_376; 
x_374 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_368, x_2, x_3);
x_375 = 1;
x_376 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_376, 0, x_365);
lean_ctor_set(x_376, 1, x_366);
lean_ctor_set(x_376, 2, x_367);
lean_ctor_set(x_376, 3, x_374);
lean_ctor_set_uint8(x_376, sizeof(void*)*4, x_375);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; 
x_377 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_368, x_2, x_3);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_377, 3);
lean_inc(x_379);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; 
x_380 = lean_ctor_get(x_377, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_377, 2);
lean_inc(x_381);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_382 = x_377;
} else {
 lean_dec_ref(x_377);
 x_382 = lean_box(0);
}
x_383 = 0;
if (lean_is_scalar(x_382)) {
 x_384 = lean_alloc_ctor(1, 4, 1);
} else {
 x_384 = x_382;
}
lean_ctor_set(x_384, 0, x_379);
lean_ctor_set(x_384, 1, x_380);
lean_ctor_set(x_384, 2, x_381);
lean_ctor_set(x_384, 3, x_379);
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_383);
x_385 = 1;
x_386 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_386, 0, x_365);
lean_ctor_set(x_386, 1, x_366);
lean_ctor_set(x_386, 2, x_367);
lean_ctor_set(x_386, 3, x_384);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_385);
return x_386;
}
else
{
uint8_t x_387; 
x_387 = lean_ctor_get_uint8(x_379, sizeof(void*)*4);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; lean_object* x_400; 
x_388 = lean_ctor_get(x_377, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_377, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_390 = x_377;
} else {
 lean_dec_ref(x_377);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_379, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_379, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_379, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_379, 3);
lean_inc(x_394);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 lean_ctor_release(x_379, 2);
 lean_ctor_release(x_379, 3);
 x_395 = x_379;
} else {
 lean_dec_ref(x_379);
 x_395 = lean_box(0);
}
x_396 = 1;
if (lean_is_scalar(x_395)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_395;
}
lean_ctor_set(x_397, 0, x_365);
lean_ctor_set(x_397, 1, x_366);
lean_ctor_set(x_397, 2, x_367);
lean_ctor_set(x_397, 3, x_378);
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_396);
if (lean_is_scalar(x_390)) {
 x_398 = lean_alloc_ctor(1, 4, 1);
} else {
 x_398 = x_390;
}
lean_ctor_set(x_398, 0, x_391);
lean_ctor_set(x_398, 1, x_392);
lean_ctor_set(x_398, 2, x_393);
lean_ctor_set(x_398, 3, x_394);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_396);
x_399 = 0;
x_400 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_388);
lean_ctor_set(x_400, 2, x_389);
lean_ctor_set(x_400, 3, x_398);
lean_ctor_set_uint8(x_400, sizeof(void*)*4, x_399);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; 
x_401 = lean_ctor_get(x_377, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_377, 2);
lean_inc(x_402);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_403 = x_377;
} else {
 lean_dec_ref(x_377);
 x_403 = lean_box(0);
}
x_404 = 0;
if (lean_is_scalar(x_403)) {
 x_405 = lean_alloc_ctor(1, 4, 1);
} else {
 x_405 = x_403;
}
lean_ctor_set(x_405, 0, x_378);
lean_ctor_set(x_405, 1, x_401);
lean_ctor_set(x_405, 2, x_402);
lean_ctor_set(x_405, 3, x_379);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_404);
x_406 = 1;
x_407 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_407, 0, x_365);
lean_ctor_set(x_407, 1, x_366);
lean_ctor_set(x_407, 2, x_367);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
return x_407;
}
}
}
else
{
uint8_t x_408; 
x_408 = lean_ctor_get_uint8(x_378, sizeof(void*)*4);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; 
x_409 = lean_ctor_get(x_377, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_377, 2);
lean_inc(x_410);
x_411 = lean_ctor_get(x_377, 3);
lean_inc(x_411);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_412 = x_377;
} else {
 lean_dec_ref(x_377);
 x_412 = lean_box(0);
}
x_413 = lean_ctor_get(x_378, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_378, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_378, 2);
lean_inc(x_415);
x_416 = lean_ctor_get(x_378, 3);
lean_inc(x_416);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_417 = x_378;
} else {
 lean_dec_ref(x_378);
 x_417 = lean_box(0);
}
x_418 = 1;
if (lean_is_scalar(x_417)) {
 x_419 = lean_alloc_ctor(1, 4, 1);
} else {
 x_419 = x_417;
}
lean_ctor_set(x_419, 0, x_365);
lean_ctor_set(x_419, 1, x_366);
lean_ctor_set(x_419, 2, x_367);
lean_ctor_set(x_419, 3, x_413);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
if (lean_is_scalar(x_412)) {
 x_420 = lean_alloc_ctor(1, 4, 1);
} else {
 x_420 = x_412;
}
lean_ctor_set(x_420, 0, x_416);
lean_ctor_set(x_420, 1, x_409);
lean_ctor_set(x_420, 2, x_410);
lean_ctor_set(x_420, 3, x_411);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_418);
x_421 = 0;
x_422 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_414);
lean_ctor_set(x_422, 2, x_415);
lean_ctor_set(x_422, 3, x_420);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
return x_422;
}
else
{
lean_object* x_423; 
x_423 = lean_ctor_get(x_377, 3);
lean_inc(x_423);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; 
x_424 = lean_ctor_get(x_377, 1);
lean_inc(x_424);
x_425 = lean_ctor_get(x_377, 2);
lean_inc(x_425);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_426 = x_377;
} else {
 lean_dec_ref(x_377);
 x_426 = lean_box(0);
}
x_427 = 0;
if (lean_is_scalar(x_426)) {
 x_428 = lean_alloc_ctor(1, 4, 1);
} else {
 x_428 = x_426;
}
lean_ctor_set(x_428, 0, x_378);
lean_ctor_set(x_428, 1, x_424);
lean_ctor_set(x_428, 2, x_425);
lean_ctor_set(x_428, 3, x_423);
lean_ctor_set_uint8(x_428, sizeof(void*)*4, x_427);
x_429 = 1;
x_430 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_430, 0, x_365);
lean_ctor_set(x_430, 1, x_366);
lean_ctor_set(x_430, 2, x_367);
lean_ctor_set(x_430, 3, x_428);
lean_ctor_set_uint8(x_430, sizeof(void*)*4, x_429);
return x_430;
}
else
{
uint8_t x_431; 
x_431 = lean_ctor_get_uint8(x_423, sizeof(void*)*4);
if (x_431 == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; 
x_432 = lean_ctor_get(x_377, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_377, 2);
lean_inc(x_433);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_434 = x_377;
} else {
 lean_dec_ref(x_377);
 x_434 = lean_box(0);
}
x_435 = lean_ctor_get(x_423, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_423, 1);
lean_inc(x_436);
x_437 = lean_ctor_get(x_423, 2);
lean_inc(x_437);
x_438 = lean_ctor_get(x_423, 3);
lean_inc(x_438);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 lean_ctor_release(x_423, 2);
 lean_ctor_release(x_423, 3);
 x_439 = x_423;
} else {
 lean_dec_ref(x_423);
 x_439 = lean_box(0);
}
x_440 = 1;
lean_inc(x_378);
if (lean_is_scalar(x_439)) {
 x_441 = lean_alloc_ctor(1, 4, 1);
} else {
 x_441 = x_439;
}
lean_ctor_set(x_441, 0, x_365);
lean_ctor_set(x_441, 1, x_366);
lean_ctor_set(x_441, 2, x_367);
lean_ctor_set(x_441, 3, x_378);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_442 = x_378;
} else {
 lean_dec_ref(x_378);
 x_442 = lean_box(0);
}
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_440);
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_435);
lean_ctor_set(x_443, 1, x_436);
lean_ctor_set(x_443, 2, x_437);
lean_ctor_set(x_443, 3, x_438);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_440);
x_444 = 0;
if (lean_is_scalar(x_434)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_434;
}
lean_ctor_set(x_445, 0, x_441);
lean_ctor_set(x_445, 1, x_432);
lean_ctor_set(x_445, 2, x_433);
lean_ctor_set(x_445, 3, x_443);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_444);
return x_445;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; uint8_t x_457; lean_object* x_458; 
x_446 = lean_ctor_get(x_377, 1);
lean_inc(x_446);
x_447 = lean_ctor_get(x_377, 2);
lean_inc(x_447);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_448 = x_377;
} else {
 lean_dec_ref(x_377);
 x_448 = lean_box(0);
}
x_449 = lean_ctor_get(x_378, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_378, 1);
lean_inc(x_450);
x_451 = lean_ctor_get(x_378, 2);
lean_inc(x_451);
x_452 = lean_ctor_get(x_378, 3);
lean_inc(x_452);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_453 = x_378;
} else {
 lean_dec_ref(x_378);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 4, 1);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_449);
lean_ctor_set(x_454, 1, x_450);
lean_ctor_set(x_454, 2, x_451);
lean_ctor_set(x_454, 3, x_452);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_431);
x_455 = 0;
if (lean_is_scalar(x_448)) {
 x_456 = lean_alloc_ctor(1, 4, 1);
} else {
 x_456 = x_448;
}
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_446);
lean_ctor_set(x_456, 2, x_447);
lean_ctor_set(x_456, 3, x_423);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_455);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_365);
lean_ctor_set(x_458, 1, x_366);
lean_ctor_set(x_458, 2, x_367);
lean_ctor_set(x_458, 3, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
}
}
}
}
}
}
else
{
uint8_t x_459; 
x_459 = l_Std_RBNode_isRed___rarg(x_365);
if (x_459 == 0)
{
lean_object* x_460; uint8_t x_461; lean_object* x_462; 
x_460 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_365, x_2, x_3);
x_461 = 1;
x_462 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_366);
lean_ctor_set(x_462, 2, x_367);
lean_ctor_set(x_462, 3, x_368);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
return x_462;
}
else
{
lean_object* x_463; lean_object* x_464; 
x_463 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_365, x_2, x_3);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; 
x_465 = lean_ctor_get(x_463, 3);
lean_inc(x_465);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; lean_object* x_470; uint8_t x_471; lean_object* x_472; 
x_466 = lean_ctor_get(x_463, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_463, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_468 = x_463;
} else {
 lean_dec_ref(x_463);
 x_468 = lean_box(0);
}
x_469 = 0;
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(1, 4, 1);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_465);
lean_ctor_set(x_470, 1, x_466);
lean_ctor_set(x_470, 2, x_467);
lean_ctor_set(x_470, 3, x_465);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_469);
x_471 = 1;
x_472 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_366);
lean_ctor_set(x_472, 2, x_367);
lean_ctor_set(x_472, 3, x_368);
lean_ctor_set_uint8(x_472, sizeof(void*)*4, x_471);
return x_472;
}
else
{
uint8_t x_473; 
x_473 = lean_ctor_get_uint8(x_465, sizeof(void*)*4);
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; 
x_474 = lean_ctor_get(x_463, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_463, 2);
lean_inc(x_475);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_476 = x_463;
} else {
 lean_dec_ref(x_463);
 x_476 = lean_box(0);
}
x_477 = lean_ctor_get(x_465, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_465, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_465, 2);
lean_inc(x_479);
x_480 = lean_ctor_get(x_465, 3);
lean_inc(x_480);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 lean_ctor_release(x_465, 2);
 lean_ctor_release(x_465, 3);
 x_481 = x_465;
} else {
 lean_dec_ref(x_465);
 x_481 = lean_box(0);
}
x_482 = 1;
if (lean_is_scalar(x_481)) {
 x_483 = lean_alloc_ctor(1, 4, 1);
} else {
 x_483 = x_481;
}
lean_ctor_set(x_483, 0, x_464);
lean_ctor_set(x_483, 1, x_474);
lean_ctor_set(x_483, 2, x_475);
lean_ctor_set(x_483, 3, x_477);
lean_ctor_set_uint8(x_483, sizeof(void*)*4, x_482);
if (lean_is_scalar(x_476)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_476;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_366);
lean_ctor_set(x_484, 2, x_367);
lean_ctor_set(x_484, 3, x_368);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_482);
x_485 = 0;
x_486 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_478);
lean_ctor_set(x_486, 2, x_479);
lean_ctor_set(x_486, 3, x_484);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_485);
return x_486;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; lean_object* x_491; uint8_t x_492; lean_object* x_493; 
x_487 = lean_ctor_get(x_463, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_463, 2);
lean_inc(x_488);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_489 = x_463;
} else {
 lean_dec_ref(x_463);
 x_489 = lean_box(0);
}
x_490 = 0;
if (lean_is_scalar(x_489)) {
 x_491 = lean_alloc_ctor(1, 4, 1);
} else {
 x_491 = x_489;
}
lean_ctor_set(x_491, 0, x_464);
lean_ctor_set(x_491, 1, x_487);
lean_ctor_set(x_491, 2, x_488);
lean_ctor_set(x_491, 3, x_465);
lean_ctor_set_uint8(x_491, sizeof(void*)*4, x_490);
x_492 = 1;
x_493 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_366);
lean_ctor_set(x_493, 2, x_367);
lean_ctor_set(x_493, 3, x_368);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_492);
return x_493;
}
}
}
else
{
uint8_t x_494; 
x_494 = lean_ctor_get_uint8(x_464, sizeof(void*)*4);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; lean_object* x_508; 
x_495 = lean_ctor_get(x_463, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_463, 2);
lean_inc(x_496);
x_497 = lean_ctor_get(x_463, 3);
lean_inc(x_497);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_498 = x_463;
} else {
 lean_dec_ref(x_463);
 x_498 = lean_box(0);
}
x_499 = lean_ctor_get(x_464, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_464, 1);
lean_inc(x_500);
x_501 = lean_ctor_get(x_464, 2);
lean_inc(x_501);
x_502 = lean_ctor_get(x_464, 3);
lean_inc(x_502);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_503 = x_464;
} else {
 lean_dec_ref(x_464);
 x_503 = lean_box(0);
}
x_504 = 1;
if (lean_is_scalar(x_503)) {
 x_505 = lean_alloc_ctor(1, 4, 1);
} else {
 x_505 = x_503;
}
lean_ctor_set(x_505, 0, x_499);
lean_ctor_set(x_505, 1, x_500);
lean_ctor_set(x_505, 2, x_501);
lean_ctor_set(x_505, 3, x_502);
lean_ctor_set_uint8(x_505, sizeof(void*)*4, x_504);
if (lean_is_scalar(x_498)) {
 x_506 = lean_alloc_ctor(1, 4, 1);
} else {
 x_506 = x_498;
}
lean_ctor_set(x_506, 0, x_497);
lean_ctor_set(x_506, 1, x_366);
lean_ctor_set(x_506, 2, x_367);
lean_ctor_set(x_506, 3, x_368);
lean_ctor_set_uint8(x_506, sizeof(void*)*4, x_504);
x_507 = 0;
x_508 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_495);
lean_ctor_set(x_508, 2, x_496);
lean_ctor_set(x_508, 3, x_506);
lean_ctor_set_uint8(x_508, sizeof(void*)*4, x_507);
return x_508;
}
else
{
lean_object* x_509; 
x_509 = lean_ctor_get(x_463, 3);
lean_inc(x_509);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; lean_object* x_514; uint8_t x_515; lean_object* x_516; 
x_510 = lean_ctor_get(x_463, 1);
lean_inc(x_510);
x_511 = lean_ctor_get(x_463, 2);
lean_inc(x_511);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_512 = x_463;
} else {
 lean_dec_ref(x_463);
 x_512 = lean_box(0);
}
x_513 = 0;
if (lean_is_scalar(x_512)) {
 x_514 = lean_alloc_ctor(1, 4, 1);
} else {
 x_514 = x_512;
}
lean_ctor_set(x_514, 0, x_464);
lean_ctor_set(x_514, 1, x_510);
lean_ctor_set(x_514, 2, x_511);
lean_ctor_set(x_514, 3, x_509);
lean_ctor_set_uint8(x_514, sizeof(void*)*4, x_513);
x_515 = 1;
x_516 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_366);
lean_ctor_set(x_516, 2, x_367);
lean_ctor_set(x_516, 3, x_368);
lean_ctor_set_uint8(x_516, sizeof(void*)*4, x_515);
return x_516;
}
else
{
uint8_t x_517; 
x_517 = lean_ctor_get_uint8(x_509, sizeof(void*)*4);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; uint8_t x_530; lean_object* x_531; 
x_518 = lean_ctor_get(x_463, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_463, 2);
lean_inc(x_519);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_520 = x_463;
} else {
 lean_dec_ref(x_463);
 x_520 = lean_box(0);
}
x_521 = lean_ctor_get(x_509, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_509, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_509, 2);
lean_inc(x_523);
x_524 = lean_ctor_get(x_509, 3);
lean_inc(x_524);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 lean_ctor_release(x_509, 2);
 lean_ctor_release(x_509, 3);
 x_525 = x_509;
} else {
 lean_dec_ref(x_509);
 x_525 = lean_box(0);
}
x_526 = 1;
lean_inc(x_464);
if (lean_is_scalar(x_525)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_525;
}
lean_ctor_set(x_527, 0, x_464);
lean_ctor_set(x_527, 1, x_518);
lean_ctor_set(x_527, 2, x_519);
lean_ctor_set(x_527, 3, x_521);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_528 = x_464;
} else {
 lean_dec_ref(x_464);
 x_528 = lean_box(0);
}
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(1, 4, 1);
} else {
 x_529 = x_528;
}
lean_ctor_set(x_529, 0, x_524);
lean_ctor_set(x_529, 1, x_366);
lean_ctor_set(x_529, 2, x_367);
lean_ctor_set(x_529, 3, x_368);
lean_ctor_set_uint8(x_529, sizeof(void*)*4, x_526);
x_530 = 0;
if (lean_is_scalar(x_520)) {
 x_531 = lean_alloc_ctor(1, 4, 1);
} else {
 x_531 = x_520;
}
lean_ctor_set(x_531, 0, x_527);
lean_ctor_set(x_531, 1, x_522);
lean_ctor_set(x_531, 2, x_523);
lean_ctor_set(x_531, 3, x_529);
lean_ctor_set_uint8(x_531, sizeof(void*)*4, x_530);
return x_531;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; uint8_t x_543; lean_object* x_544; 
x_532 = lean_ctor_get(x_463, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_463, 2);
lean_inc(x_533);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_534 = x_463;
} else {
 lean_dec_ref(x_463);
 x_534 = lean_box(0);
}
x_535 = lean_ctor_get(x_464, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_464, 1);
lean_inc(x_536);
x_537 = lean_ctor_get(x_464, 2);
lean_inc(x_537);
x_538 = lean_ctor_get(x_464, 3);
lean_inc(x_538);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_539 = x_464;
} else {
 lean_dec_ref(x_464);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 4, 1);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_535);
lean_ctor_set(x_540, 1, x_536);
lean_ctor_set(x_540, 2, x_537);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_517);
x_541 = 0;
if (lean_is_scalar(x_534)) {
 x_542 = lean_alloc_ctor(1, 4, 1);
} else {
 x_542 = x_534;
}
lean_ctor_set(x_542, 0, x_540);
lean_ctor_set(x_542, 1, x_532);
lean_ctor_set(x_542, 2, x_533);
lean_ctor_set(x_542, 3, x_509);
lean_ctor_set_uint8(x_542, sizeof(void*)*4, x_541);
x_543 = 1;
x_544 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_366);
lean_ctor_set(x_544, 2, x_367);
lean_ctor_set(x_544, 3, x_368);
lean_ctor_set_uint8(x_544, sizeof(void*)*4, x_543);
return x_544;
}
}
}
}
}
}
}
}
}
}
}
lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = l_Lean_Name_quickLt(x_2, x_10);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Name_quickLt(x_10, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_10);
x_15 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_12, x_2, x_3);
x_17 = 0;
lean_ctor_set(x_1, 3, x_16);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_17);
return x_1;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_9, x_2, x_3);
x_19 = 0;
lean_ctor_set(x_1, 0, x_18);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = l_Lean_Name_quickLt(x_2, x_21);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Name_quickLt(x_21, x_2);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_21);
x_26 = 0;
x_27 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set(x_27, 2, x_3);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_26);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_23, x_2, x_3);
x_29 = 0;
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_22);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_29);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_20, x_2, x_3);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = l_Lean_Name_quickLt(x_2, x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Name_quickLt(x_36, x_2);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_37);
lean_dec(x_36);
x_41 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_41);
return x_1;
}
else
{
uint8_t x_42; 
x_42 = l_Std_RBNode_isRed___rarg(x_38);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_38, x_2, x_3);
x_44 = 1;
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_44);
return x_1;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_38, x_2, x_3);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 3);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_45, 3);
lean_dec(x_49);
x_50 = lean_ctor_get(x_45, 0);
lean_dec(x_50);
x_51 = 0;
lean_ctor_set(x_45, 0, x_47);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_51);
x_52 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_52);
return x_1;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_45, 1);
x_54 = lean_ctor_get(x_45, 2);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_45);
x_55 = 0;
x_56 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_56, 2, x_54);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_55);
x_57 = 1;
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_57);
return x_1;
}
}
else
{
uint8_t x_58; 
x_58 = lean_ctor_get_uint8(x_47, sizeof(void*)*4);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_45);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_45, 1);
x_61 = lean_ctor_get(x_45, 2);
x_62 = lean_ctor_get(x_45, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_45, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_47);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_47, 0);
x_66 = lean_ctor_get(x_47, 1);
x_67 = lean_ctor_get(x_47, 2);
x_68 = lean_ctor_get(x_47, 3);
x_69 = 1;
lean_ctor_set(x_47, 3, x_46);
lean_ctor_set(x_47, 2, x_37);
lean_ctor_set(x_47, 1, x_36);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_69);
lean_ctor_set(x_45, 3, x_68);
lean_ctor_set(x_45, 2, x_67);
lean_ctor_set(x_45, 1, x_66);
lean_ctor_set(x_45, 0, x_65);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_69);
x_70 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_61);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_1, 0, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_70);
return x_1;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; 
x_71 = lean_ctor_get(x_47, 0);
x_72 = lean_ctor_get(x_47, 1);
x_73 = lean_ctor_get(x_47, 2);
x_74 = lean_ctor_get(x_47, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_47);
x_75 = 1;
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_35);
lean_ctor_set(x_76, 1, x_36);
lean_ctor_set(x_76, 2, x_37);
lean_ctor_set(x_76, 3, x_46);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_75);
lean_ctor_set(x_45, 3, x_74);
lean_ctor_set(x_45, 2, x_73);
lean_ctor_set(x_45, 1, x_72);
lean_ctor_set(x_45, 0, x_71);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_75);
x_77 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_61);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_1, 0, x_76);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_77);
return x_1;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_78 = lean_ctor_get(x_45, 1);
x_79 = lean_ctor_get(x_45, 2);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_45);
x_80 = lean_ctor_get(x_47, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_47, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_47, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_47, 3);
lean_inc(x_83);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_84 = x_47;
} else {
 lean_dec_ref(x_47);
 x_84 = lean_box(0);
}
x_85 = 1;
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(1, 4, 1);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_35);
lean_ctor_set(x_86, 1, x_36);
lean_ctor_set(x_86, 2, x_37);
lean_ctor_set(x_86, 3, x_46);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_85);
x_87 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_81);
lean_ctor_set(x_87, 2, x_82);
lean_ctor_set(x_87, 3, x_83);
lean_ctor_set_uint8(x_87, sizeof(void*)*4, x_85);
x_88 = 0;
lean_ctor_set(x_1, 3, x_87);
lean_ctor_set(x_1, 2, x_79);
lean_ctor_set(x_1, 1, x_78);
lean_ctor_set(x_1, 0, x_86);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_88);
return x_1;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_45);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_45, 3);
lean_dec(x_90);
x_91 = lean_ctor_get(x_45, 0);
lean_dec(x_91);
x_92 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_92);
x_93 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_93);
return x_1;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_45, 1);
x_95 = lean_ctor_get(x_45, 2);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_45);
x_96 = 0;
x_97 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_97, 0, x_46);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_47);
lean_ctor_set_uint8(x_97, sizeof(void*)*4, x_96);
x_98 = 1;
lean_ctor_set(x_1, 3, x_97);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_98);
return x_1;
}
}
}
}
else
{
uint8_t x_99; 
x_99 = lean_ctor_get_uint8(x_46, sizeof(void*)*4);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_45);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_45, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_46);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; 
x_103 = lean_ctor_get(x_46, 0);
x_104 = lean_ctor_get(x_46, 1);
x_105 = lean_ctor_get(x_46, 2);
x_106 = lean_ctor_get(x_46, 3);
x_107 = 1;
lean_ctor_set(x_46, 3, x_103);
lean_ctor_set(x_46, 2, x_37);
lean_ctor_set(x_46, 1, x_36);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_107);
lean_ctor_set(x_45, 0, x_106);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_107);
x_108 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_105);
lean_ctor_set(x_1, 1, x_104);
lean_ctor_set(x_1, 0, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_108);
return x_1;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; uint8_t x_115; 
x_109 = lean_ctor_get(x_46, 0);
x_110 = lean_ctor_get(x_46, 1);
x_111 = lean_ctor_get(x_46, 2);
x_112 = lean_ctor_get(x_46, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_46);
x_113 = 1;
x_114 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_114, 0, x_35);
lean_ctor_set(x_114, 1, x_36);
lean_ctor_set(x_114, 2, x_37);
lean_ctor_set(x_114, 3, x_109);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_113);
lean_ctor_set(x_45, 0, x_112);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_113);
x_115 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_111);
lean_ctor_set(x_1, 1, x_110);
lean_ctor_set(x_1, 0, x_114);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_115);
return x_1;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_116 = lean_ctor_get(x_45, 1);
x_117 = lean_ctor_get(x_45, 2);
x_118 = lean_ctor_get(x_45, 3);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_45);
x_119 = lean_ctor_get(x_46, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_46, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_46, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_46, 3);
lean_inc(x_122);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_123 = x_46;
} else {
 lean_dec_ref(x_46);
 x_123 = lean_box(0);
}
x_124 = 1;
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(1, 4, 1);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_35);
lean_ctor_set(x_125, 1, x_36);
lean_ctor_set(x_125, 2, x_37);
lean_ctor_set(x_125, 3, x_119);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_124);
x_126 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_116);
lean_ctor_set(x_126, 2, x_117);
lean_ctor_set(x_126, 3, x_118);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_124);
x_127 = 0;
lean_ctor_set(x_1, 3, x_126);
lean_ctor_set(x_1, 2, x_121);
lean_ctor_set(x_1, 1, x_120);
lean_ctor_set(x_1, 0, x_125);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_127);
return x_1;
}
}
else
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_45, 3);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_45);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_45, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_45, 0);
lean_dec(x_131);
x_132 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_132);
x_133 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_133);
return x_1;
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; uint8_t x_138; 
x_134 = lean_ctor_get(x_45, 1);
x_135 = lean_ctor_get(x_45, 2);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_45);
x_136 = 0;
x_137 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_137, 0, x_46);
lean_ctor_set(x_137, 1, x_134);
lean_ctor_set(x_137, 2, x_135);
lean_ctor_set(x_137, 3, x_128);
lean_ctor_set_uint8(x_137, sizeof(void*)*4, x_136);
x_138 = 1;
lean_ctor_set(x_1, 3, x_137);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_138);
return x_1;
}
}
else
{
uint8_t x_139; 
x_139 = lean_ctor_get_uint8(x_128, sizeof(void*)*4);
if (x_139 == 0)
{
uint8_t x_140; 
lean_free_object(x_1);
x_140 = !lean_is_exclusive(x_45);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_45, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_45, 0);
lean_dec(x_142);
x_143 = !lean_is_exclusive(x_128);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; 
x_144 = lean_ctor_get(x_128, 0);
x_145 = lean_ctor_get(x_128, 1);
x_146 = lean_ctor_get(x_128, 2);
x_147 = lean_ctor_get(x_128, 3);
x_148 = 1;
lean_inc(x_46);
lean_ctor_set(x_128, 3, x_46);
lean_ctor_set(x_128, 2, x_37);
lean_ctor_set(x_128, 1, x_36);
lean_ctor_set(x_128, 0, x_35);
x_149 = !lean_is_exclusive(x_46);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_150 = lean_ctor_get(x_46, 3);
lean_dec(x_150);
x_151 = lean_ctor_get(x_46, 2);
lean_dec(x_151);
x_152 = lean_ctor_get(x_46, 1);
lean_dec(x_152);
x_153 = lean_ctor_get(x_46, 0);
lean_dec(x_153);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_148);
lean_ctor_set(x_46, 3, x_147);
lean_ctor_set(x_46, 2, x_146);
lean_ctor_set(x_46, 1, x_145);
lean_ctor_set(x_46, 0, x_144);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_148);
x_154 = 0;
lean_ctor_set(x_45, 3, x_46);
lean_ctor_set(x_45, 0, x_128);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_154);
return x_45;
}
else
{
lean_object* x_155; uint8_t x_156; 
lean_dec(x_46);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_148);
x_155 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_155, 0, x_144);
lean_ctor_set(x_155, 1, x_145);
lean_ctor_set(x_155, 2, x_146);
lean_ctor_set(x_155, 3, x_147);
lean_ctor_set_uint8(x_155, sizeof(void*)*4, x_148);
x_156 = 0;
lean_ctor_set(x_45, 3, x_155);
lean_ctor_set(x_45, 0, x_128);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_156);
return x_45;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_157 = lean_ctor_get(x_128, 0);
x_158 = lean_ctor_get(x_128, 1);
x_159 = lean_ctor_get(x_128, 2);
x_160 = lean_ctor_get(x_128, 3);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_128);
x_161 = 1;
lean_inc(x_46);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_35);
lean_ctor_set(x_162, 1, x_36);
lean_ctor_set(x_162, 2, x_37);
lean_ctor_set(x_162, 3, x_46);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_163 = x_46;
} else {
 lean_dec_ref(x_46);
 x_163 = lean_box(0);
}
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_161);
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 4, 1);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_157);
lean_ctor_set(x_164, 1, x_158);
lean_ctor_set(x_164, 2, x_159);
lean_ctor_set(x_164, 3, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_161);
x_165 = 0;
lean_ctor_set(x_45, 3, x_164);
lean_ctor_set(x_45, 0, x_162);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_165);
return x_45;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; 
x_166 = lean_ctor_get(x_45, 1);
x_167 = lean_ctor_get(x_45, 2);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_45);
x_168 = lean_ctor_get(x_128, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_128, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_128, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_128, 3);
lean_inc(x_171);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 x_172 = x_128;
} else {
 lean_dec_ref(x_128);
 x_172 = lean_box(0);
}
x_173 = 1;
lean_inc(x_46);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(1, 4, 1);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_35);
lean_ctor_set(x_174, 1, x_36);
lean_ctor_set(x_174, 2, x_37);
lean_ctor_set(x_174, 3, x_46);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_175 = x_46;
} else {
 lean_dec_ref(x_46);
 x_175 = lean_box(0);
}
lean_ctor_set_uint8(x_174, sizeof(void*)*4, x_173);
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 4, 1);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_168);
lean_ctor_set(x_176, 1, x_169);
lean_ctor_set(x_176, 2, x_170);
lean_ctor_set(x_176, 3, x_171);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_173);
x_177 = 0;
x_178 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_166);
lean_ctor_set(x_178, 2, x_167);
lean_ctor_set(x_178, 3, x_176);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_177);
return x_178;
}
}
else
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_45);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_45, 3);
lean_dec(x_180);
x_181 = lean_ctor_get(x_45, 0);
lean_dec(x_181);
x_182 = !lean_is_exclusive(x_46);
if (x_182 == 0)
{
uint8_t x_183; uint8_t x_184; 
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_139);
x_183 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_183);
x_184 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_184);
return x_1;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_191; 
x_185 = lean_ctor_get(x_46, 0);
x_186 = lean_ctor_get(x_46, 1);
x_187 = lean_ctor_get(x_46, 2);
x_188 = lean_ctor_get(x_46, 3);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_46);
x_189 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_189, 0, x_185);
lean_ctor_set(x_189, 1, x_186);
lean_ctor_set(x_189, 2, x_187);
lean_ctor_set(x_189, 3, x_188);
lean_ctor_set_uint8(x_189, sizeof(void*)*4, x_139);
x_190 = 0;
lean_ctor_set(x_45, 0, x_189);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_190);
x_191 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_191);
return x_1;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; uint8_t x_202; 
x_192 = lean_ctor_get(x_45, 1);
x_193 = lean_ctor_get(x_45, 2);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_45);
x_194 = lean_ctor_get(x_46, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_46, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_46, 2);
lean_inc(x_196);
x_197 = lean_ctor_get(x_46, 3);
lean_inc(x_197);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_198 = x_46;
} else {
 lean_dec_ref(x_46);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 4, 1);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_194);
lean_ctor_set(x_199, 1, x_195);
lean_ctor_set(x_199, 2, x_196);
lean_ctor_set(x_199, 3, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_139);
x_200 = 0;
x_201 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_192);
lean_ctor_set(x_201, 2, x_193);
lean_ctor_set(x_201, 3, x_128);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_200);
x_202 = 1;
lean_ctor_set(x_1, 3, x_201);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
}
}
}
}
}
}
}
}
else
{
uint8_t x_203; 
x_203 = l_Std_RBNode_isRed___rarg(x_35);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_35, x_2, x_3);
x_205 = 1;
lean_ctor_set(x_1, 0, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_205);
return x_1;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_35, x_2, x_3);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_206, 3);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_206);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; uint8_t x_213; 
x_210 = lean_ctor_get(x_206, 3);
lean_dec(x_210);
x_211 = lean_ctor_get(x_206, 0);
lean_dec(x_211);
x_212 = 0;
lean_ctor_set(x_206, 0, x_208);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_212);
x_213 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_213);
return x_1;
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_206, 1);
x_215 = lean_ctor_get(x_206, 2);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_206);
x_216 = 0;
x_217 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_217, 0, x_208);
lean_ctor_set(x_217, 1, x_214);
lean_ctor_set(x_217, 2, x_215);
lean_ctor_set(x_217, 3, x_208);
lean_ctor_set_uint8(x_217, sizeof(void*)*4, x_216);
x_218 = 1;
lean_ctor_set(x_1, 0, x_217);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_218);
return x_1;
}
}
else
{
uint8_t x_219; 
x_219 = lean_ctor_get_uint8(x_208, sizeof(void*)*4);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_206);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_221 = lean_ctor_get(x_206, 1);
x_222 = lean_ctor_get(x_206, 2);
x_223 = lean_ctor_get(x_206, 3);
lean_dec(x_223);
x_224 = lean_ctor_get(x_206, 0);
lean_dec(x_224);
x_225 = !lean_is_exclusive(x_208);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_231; 
x_226 = lean_ctor_get(x_208, 0);
x_227 = lean_ctor_get(x_208, 1);
x_228 = lean_ctor_get(x_208, 2);
x_229 = lean_ctor_get(x_208, 3);
x_230 = 1;
lean_ctor_set(x_208, 3, x_226);
lean_ctor_set(x_208, 2, x_222);
lean_ctor_set(x_208, 1, x_221);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_230);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_229);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_230);
x_231 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_208);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_231);
return x_1;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; uint8_t x_238; 
x_232 = lean_ctor_get(x_208, 0);
x_233 = lean_ctor_get(x_208, 1);
x_234 = lean_ctor_get(x_208, 2);
x_235 = lean_ctor_get(x_208, 3);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_208);
x_236 = 1;
x_237 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_237, 0, x_207);
lean_ctor_set(x_237, 1, x_221);
lean_ctor_set(x_237, 2, x_222);
lean_ctor_set(x_237, 3, x_232);
lean_ctor_set_uint8(x_237, sizeof(void*)*4, x_236);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_235);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_236);
x_238 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_234);
lean_ctor_set(x_1, 1, x_233);
lean_ctor_set(x_1, 0, x_237);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_238);
return x_1;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_239 = lean_ctor_get(x_206, 1);
x_240 = lean_ctor_get(x_206, 2);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_206);
x_241 = lean_ctor_get(x_208, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_208, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_208, 2);
lean_inc(x_243);
x_244 = lean_ctor_get(x_208, 3);
lean_inc(x_244);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 lean_ctor_release(x_208, 3);
 x_245 = x_208;
} else {
 lean_dec_ref(x_208);
 x_245 = lean_box(0);
}
x_246 = 1;
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(1, 4, 1);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_207);
lean_ctor_set(x_247, 1, x_239);
lean_ctor_set(x_247, 2, x_240);
lean_ctor_set(x_247, 3, x_241);
lean_ctor_set_uint8(x_247, sizeof(void*)*4, x_246);
x_248 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_248, 0, x_244);
lean_ctor_set(x_248, 1, x_36);
lean_ctor_set(x_248, 2, x_37);
lean_ctor_set(x_248, 3, x_38);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_246);
x_249 = 0;
lean_ctor_set(x_1, 3, x_248);
lean_ctor_set(x_1, 2, x_243);
lean_ctor_set(x_1, 1, x_242);
lean_ctor_set(x_1, 0, x_247);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_249);
return x_1;
}
}
else
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_206);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_254; 
x_251 = lean_ctor_get(x_206, 3);
lean_dec(x_251);
x_252 = lean_ctor_get(x_206, 0);
lean_dec(x_252);
x_253 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_253);
x_254 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_254);
return x_1;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_255 = lean_ctor_get(x_206, 1);
x_256 = lean_ctor_get(x_206, 2);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_206);
x_257 = 0;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_207);
lean_ctor_set(x_258, 1, x_255);
lean_ctor_set(x_258, 2, x_256);
lean_ctor_set(x_258, 3, x_208);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
x_259 = 1;
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
else
{
uint8_t x_260; 
x_260 = lean_ctor_get_uint8(x_207, sizeof(void*)*4);
if (x_260 == 0)
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_206);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_262 = lean_ctor_get(x_206, 1);
x_263 = lean_ctor_get(x_206, 2);
x_264 = lean_ctor_get(x_206, 3);
x_265 = lean_ctor_get(x_206, 0);
lean_dec(x_265);
x_266 = !lean_is_exclusive(x_207);
if (x_266 == 0)
{
uint8_t x_267; uint8_t x_268; 
x_267 = 1;
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_267);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_267);
x_268 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_207);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_268);
return x_1;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; uint8_t x_275; 
x_269 = lean_ctor_get(x_207, 0);
x_270 = lean_ctor_get(x_207, 1);
x_271 = lean_ctor_get(x_207, 2);
x_272 = lean_ctor_get(x_207, 3);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_207);
x_273 = 1;
x_274 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_274, 0, x_269);
lean_ctor_set(x_274, 1, x_270);
lean_ctor_set(x_274, 2, x_271);
lean_ctor_set(x_274, 3, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*4, x_273);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_273);
x_275 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_274);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_275);
return x_1;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_276 = lean_ctor_get(x_206, 1);
x_277 = lean_ctor_get(x_206, 2);
x_278 = lean_ctor_get(x_206, 3);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_206);
x_279 = lean_ctor_get(x_207, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_207, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_207, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_207, 3);
lean_inc(x_282);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_283 = x_207;
} else {
 lean_dec_ref(x_207);
 x_283 = lean_box(0);
}
x_284 = 1;
if (lean_is_scalar(x_283)) {
 x_285 = lean_alloc_ctor(1, 4, 1);
} else {
 x_285 = x_283;
}
lean_ctor_set(x_285, 0, x_279);
lean_ctor_set(x_285, 1, x_280);
lean_ctor_set(x_285, 2, x_281);
lean_ctor_set(x_285, 3, x_282);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_284);
x_286 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_286, 0, x_278);
lean_ctor_set(x_286, 1, x_36);
lean_ctor_set(x_286, 2, x_37);
lean_ctor_set(x_286, 3, x_38);
lean_ctor_set_uint8(x_286, sizeof(void*)*4, x_284);
x_287 = 0;
lean_ctor_set(x_1, 3, x_286);
lean_ctor_set(x_1, 2, x_277);
lean_ctor_set(x_1, 1, x_276);
lean_ctor_set(x_1, 0, x_285);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_287);
return x_1;
}
}
else
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_206, 3);
lean_inc(x_288);
if (lean_obj_tag(x_288) == 0)
{
uint8_t x_289; 
x_289 = !lean_is_exclusive(x_206);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_293; 
x_290 = lean_ctor_get(x_206, 3);
lean_dec(x_290);
x_291 = lean_ctor_get(x_206, 0);
lean_dec(x_291);
x_292 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_292);
x_293 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_293);
return x_1;
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_206, 1);
x_295 = lean_ctor_get(x_206, 2);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_206);
x_296 = 0;
x_297 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_297, 0, x_207);
lean_ctor_set(x_297, 1, x_294);
lean_ctor_set(x_297, 2, x_295);
lean_ctor_set(x_297, 3, x_288);
lean_ctor_set_uint8(x_297, sizeof(void*)*4, x_296);
x_298 = 1;
lean_ctor_set(x_1, 0, x_297);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_298);
return x_1;
}
}
else
{
uint8_t x_299; 
x_299 = lean_ctor_get_uint8(x_288, sizeof(void*)*4);
if (x_299 == 0)
{
uint8_t x_300; 
lean_free_object(x_1);
x_300 = !lean_is_exclusive(x_206);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_301 = lean_ctor_get(x_206, 1);
x_302 = lean_ctor_get(x_206, 2);
x_303 = lean_ctor_get(x_206, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_206, 0);
lean_dec(x_304);
x_305 = !lean_is_exclusive(x_288);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_311; 
x_306 = lean_ctor_get(x_288, 0);
x_307 = lean_ctor_get(x_288, 1);
x_308 = lean_ctor_get(x_288, 2);
x_309 = lean_ctor_get(x_288, 3);
x_310 = 1;
lean_inc(x_207);
lean_ctor_set(x_288, 3, x_306);
lean_ctor_set(x_288, 2, x_302);
lean_ctor_set(x_288, 1, x_301);
lean_ctor_set(x_288, 0, x_207);
x_311 = !lean_is_exclusive(x_207);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_312 = lean_ctor_get(x_207, 3);
lean_dec(x_312);
x_313 = lean_ctor_get(x_207, 2);
lean_dec(x_313);
x_314 = lean_ctor_get(x_207, 1);
lean_dec(x_314);
x_315 = lean_ctor_get(x_207, 0);
lean_dec(x_315);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
lean_ctor_set(x_207, 3, x_38);
lean_ctor_set(x_207, 2, x_37);
lean_ctor_set(x_207, 1, x_36);
lean_ctor_set(x_207, 0, x_309);
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_310);
x_316 = 0;
lean_ctor_set(x_206, 3, x_207);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_316);
return x_206;
}
else
{
lean_object* x_317; uint8_t x_318; 
lean_dec(x_207);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
x_317 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_36);
lean_ctor_set(x_317, 2, x_37);
lean_ctor_set(x_317, 3, x_38);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_310);
x_318 = 0;
lean_ctor_set(x_206, 3, x_317);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_318);
return x_206;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_319 = lean_ctor_get(x_288, 0);
x_320 = lean_ctor_get(x_288, 1);
x_321 = lean_ctor_get(x_288, 2);
x_322 = lean_ctor_get(x_288, 3);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_288);
x_323 = 1;
lean_inc(x_207);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_207);
lean_ctor_set(x_324, 1, x_301);
lean_ctor_set(x_324, 2, x_302);
lean_ctor_set(x_324, 3, x_319);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_325 = x_207;
} else {
 lean_dec_ref(x_207);
 x_325 = lean_box(0);
}
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_323);
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 4, 1);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_322);
lean_ctor_set(x_326, 1, x_36);
lean_ctor_set(x_326, 2, x_37);
lean_ctor_set(x_326, 3, x_38);
lean_ctor_set_uint8(x_326, sizeof(void*)*4, x_323);
x_327 = 0;
lean_ctor_set(x_206, 3, x_326);
lean_ctor_set(x_206, 2, x_321);
lean_ctor_set(x_206, 1, x_320);
lean_ctor_set(x_206, 0, x_324);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_327);
return x_206;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; 
x_328 = lean_ctor_get(x_206, 1);
x_329 = lean_ctor_get(x_206, 2);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_206);
x_330 = lean_ctor_get(x_288, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_288, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_288, 2);
lean_inc(x_332);
x_333 = lean_ctor_get(x_288, 3);
lean_inc(x_333);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 lean_ctor_release(x_288, 2);
 lean_ctor_release(x_288, 3);
 x_334 = x_288;
} else {
 lean_dec_ref(x_288);
 x_334 = lean_box(0);
}
x_335 = 1;
lean_inc(x_207);
if (lean_is_scalar(x_334)) {
 x_336 = lean_alloc_ctor(1, 4, 1);
} else {
 x_336 = x_334;
}
lean_ctor_set(x_336, 0, x_207);
lean_ctor_set(x_336, 1, x_328);
lean_ctor_set(x_336, 2, x_329);
lean_ctor_set(x_336, 3, x_330);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_337 = x_207;
} else {
 lean_dec_ref(x_207);
 x_337 = lean_box(0);
}
lean_ctor_set_uint8(x_336, sizeof(void*)*4, x_335);
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_36);
lean_ctor_set(x_338, 2, x_37);
lean_ctor_set(x_338, 3, x_38);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_335);
x_339 = 0;
x_340 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_340, 0, x_336);
lean_ctor_set(x_340, 1, x_331);
lean_ctor_set(x_340, 2, x_332);
lean_ctor_set(x_340, 3, x_338);
lean_ctor_set_uint8(x_340, sizeof(void*)*4, x_339);
return x_340;
}
}
else
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_206);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_342 = lean_ctor_get(x_206, 3);
lean_dec(x_342);
x_343 = lean_ctor_get(x_206, 0);
lean_dec(x_343);
x_344 = !lean_is_exclusive(x_207);
if (x_344 == 0)
{
uint8_t x_345; uint8_t x_346; 
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_299);
x_345 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_345);
x_346 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_346);
return x_1;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; uint8_t x_353; 
x_347 = lean_ctor_get(x_207, 0);
x_348 = lean_ctor_get(x_207, 1);
x_349 = lean_ctor_get(x_207, 2);
x_350 = lean_ctor_get(x_207, 3);
lean_inc(x_350);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_207);
x_351 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_351, 0, x_347);
lean_ctor_set(x_351, 1, x_348);
lean_ctor_set(x_351, 2, x_349);
lean_ctor_set(x_351, 3, x_350);
lean_ctor_set_uint8(x_351, sizeof(void*)*4, x_299);
x_352 = 0;
lean_ctor_set(x_206, 0, x_351);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_352);
x_353 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_353);
return x_1;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; uint8_t x_364; 
x_354 = lean_ctor_get(x_206, 1);
x_355 = lean_ctor_get(x_206, 2);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_206);
x_356 = lean_ctor_get(x_207, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_207, 1);
lean_inc(x_357);
x_358 = lean_ctor_get(x_207, 2);
lean_inc(x_358);
x_359 = lean_ctor_get(x_207, 3);
lean_inc(x_359);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_360 = x_207;
} else {
 lean_dec_ref(x_207);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 4, 1);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_356);
lean_ctor_set(x_361, 1, x_357);
lean_ctor_set(x_361, 2, x_358);
lean_ctor_set(x_361, 3, x_359);
lean_ctor_set_uint8(x_361, sizeof(void*)*4, x_299);
x_362 = 0;
x_363 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_354);
lean_ctor_set(x_363, 2, x_355);
lean_ctor_set(x_363, 3, x_288);
lean_ctor_set_uint8(x_363, sizeof(void*)*4, x_362);
x_364 = 1;
lean_ctor_set(x_1, 0, x_363);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_364);
return x_1;
}
}
}
}
}
}
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_365 = lean_ctor_get(x_1, 0);
x_366 = lean_ctor_get(x_1, 1);
x_367 = lean_ctor_get(x_1, 2);
x_368 = lean_ctor_get(x_1, 3);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_1);
x_369 = l_Lean_Name_quickLt(x_2, x_366);
if (x_369 == 0)
{
uint8_t x_370; 
x_370 = l_Lean_Name_quickLt(x_366, x_2);
if (x_370 == 0)
{
uint8_t x_371; lean_object* x_372; 
lean_dec(x_367);
lean_dec(x_366);
x_371 = 1;
x_372 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_372, 0, x_365);
lean_ctor_set(x_372, 1, x_2);
lean_ctor_set(x_372, 2, x_3);
lean_ctor_set(x_372, 3, x_368);
lean_ctor_set_uint8(x_372, sizeof(void*)*4, x_371);
return x_372;
}
else
{
uint8_t x_373; 
x_373 = l_Std_RBNode_isRed___rarg(x_368);
if (x_373 == 0)
{
lean_object* x_374; uint8_t x_375; lean_object* x_376; 
x_374 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_368, x_2, x_3);
x_375 = 1;
x_376 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_376, 0, x_365);
lean_ctor_set(x_376, 1, x_366);
lean_ctor_set(x_376, 2, x_367);
lean_ctor_set(x_376, 3, x_374);
lean_ctor_set_uint8(x_376, sizeof(void*)*4, x_375);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; 
x_377 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_368, x_2, x_3);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_377, 3);
lean_inc(x_379);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; 
x_380 = lean_ctor_get(x_377, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_377, 2);
lean_inc(x_381);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_382 = x_377;
} else {
 lean_dec_ref(x_377);
 x_382 = lean_box(0);
}
x_383 = 0;
if (lean_is_scalar(x_382)) {
 x_384 = lean_alloc_ctor(1, 4, 1);
} else {
 x_384 = x_382;
}
lean_ctor_set(x_384, 0, x_379);
lean_ctor_set(x_384, 1, x_380);
lean_ctor_set(x_384, 2, x_381);
lean_ctor_set(x_384, 3, x_379);
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_383);
x_385 = 1;
x_386 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_386, 0, x_365);
lean_ctor_set(x_386, 1, x_366);
lean_ctor_set(x_386, 2, x_367);
lean_ctor_set(x_386, 3, x_384);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_385);
return x_386;
}
else
{
uint8_t x_387; 
x_387 = lean_ctor_get_uint8(x_379, sizeof(void*)*4);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; lean_object* x_400; 
x_388 = lean_ctor_get(x_377, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_377, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_390 = x_377;
} else {
 lean_dec_ref(x_377);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_379, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_379, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_379, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_379, 3);
lean_inc(x_394);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 lean_ctor_release(x_379, 2);
 lean_ctor_release(x_379, 3);
 x_395 = x_379;
} else {
 lean_dec_ref(x_379);
 x_395 = lean_box(0);
}
x_396 = 1;
if (lean_is_scalar(x_395)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_395;
}
lean_ctor_set(x_397, 0, x_365);
lean_ctor_set(x_397, 1, x_366);
lean_ctor_set(x_397, 2, x_367);
lean_ctor_set(x_397, 3, x_378);
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_396);
if (lean_is_scalar(x_390)) {
 x_398 = lean_alloc_ctor(1, 4, 1);
} else {
 x_398 = x_390;
}
lean_ctor_set(x_398, 0, x_391);
lean_ctor_set(x_398, 1, x_392);
lean_ctor_set(x_398, 2, x_393);
lean_ctor_set(x_398, 3, x_394);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_396);
x_399 = 0;
x_400 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_388);
lean_ctor_set(x_400, 2, x_389);
lean_ctor_set(x_400, 3, x_398);
lean_ctor_set_uint8(x_400, sizeof(void*)*4, x_399);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; 
x_401 = lean_ctor_get(x_377, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_377, 2);
lean_inc(x_402);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_403 = x_377;
} else {
 lean_dec_ref(x_377);
 x_403 = lean_box(0);
}
x_404 = 0;
if (lean_is_scalar(x_403)) {
 x_405 = lean_alloc_ctor(1, 4, 1);
} else {
 x_405 = x_403;
}
lean_ctor_set(x_405, 0, x_378);
lean_ctor_set(x_405, 1, x_401);
lean_ctor_set(x_405, 2, x_402);
lean_ctor_set(x_405, 3, x_379);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_404);
x_406 = 1;
x_407 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_407, 0, x_365);
lean_ctor_set(x_407, 1, x_366);
lean_ctor_set(x_407, 2, x_367);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
return x_407;
}
}
}
else
{
uint8_t x_408; 
x_408 = lean_ctor_get_uint8(x_378, sizeof(void*)*4);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; 
x_409 = lean_ctor_get(x_377, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_377, 2);
lean_inc(x_410);
x_411 = lean_ctor_get(x_377, 3);
lean_inc(x_411);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_412 = x_377;
} else {
 lean_dec_ref(x_377);
 x_412 = lean_box(0);
}
x_413 = lean_ctor_get(x_378, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_378, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_378, 2);
lean_inc(x_415);
x_416 = lean_ctor_get(x_378, 3);
lean_inc(x_416);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_417 = x_378;
} else {
 lean_dec_ref(x_378);
 x_417 = lean_box(0);
}
x_418 = 1;
if (lean_is_scalar(x_417)) {
 x_419 = lean_alloc_ctor(1, 4, 1);
} else {
 x_419 = x_417;
}
lean_ctor_set(x_419, 0, x_365);
lean_ctor_set(x_419, 1, x_366);
lean_ctor_set(x_419, 2, x_367);
lean_ctor_set(x_419, 3, x_413);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
if (lean_is_scalar(x_412)) {
 x_420 = lean_alloc_ctor(1, 4, 1);
} else {
 x_420 = x_412;
}
lean_ctor_set(x_420, 0, x_416);
lean_ctor_set(x_420, 1, x_409);
lean_ctor_set(x_420, 2, x_410);
lean_ctor_set(x_420, 3, x_411);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_418);
x_421 = 0;
x_422 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_414);
lean_ctor_set(x_422, 2, x_415);
lean_ctor_set(x_422, 3, x_420);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
return x_422;
}
else
{
lean_object* x_423; 
x_423 = lean_ctor_get(x_377, 3);
lean_inc(x_423);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; 
x_424 = lean_ctor_get(x_377, 1);
lean_inc(x_424);
x_425 = lean_ctor_get(x_377, 2);
lean_inc(x_425);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_426 = x_377;
} else {
 lean_dec_ref(x_377);
 x_426 = lean_box(0);
}
x_427 = 0;
if (lean_is_scalar(x_426)) {
 x_428 = lean_alloc_ctor(1, 4, 1);
} else {
 x_428 = x_426;
}
lean_ctor_set(x_428, 0, x_378);
lean_ctor_set(x_428, 1, x_424);
lean_ctor_set(x_428, 2, x_425);
lean_ctor_set(x_428, 3, x_423);
lean_ctor_set_uint8(x_428, sizeof(void*)*4, x_427);
x_429 = 1;
x_430 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_430, 0, x_365);
lean_ctor_set(x_430, 1, x_366);
lean_ctor_set(x_430, 2, x_367);
lean_ctor_set(x_430, 3, x_428);
lean_ctor_set_uint8(x_430, sizeof(void*)*4, x_429);
return x_430;
}
else
{
uint8_t x_431; 
x_431 = lean_ctor_get_uint8(x_423, sizeof(void*)*4);
if (x_431 == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; 
x_432 = lean_ctor_get(x_377, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_377, 2);
lean_inc(x_433);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_434 = x_377;
} else {
 lean_dec_ref(x_377);
 x_434 = lean_box(0);
}
x_435 = lean_ctor_get(x_423, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_423, 1);
lean_inc(x_436);
x_437 = lean_ctor_get(x_423, 2);
lean_inc(x_437);
x_438 = lean_ctor_get(x_423, 3);
lean_inc(x_438);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 lean_ctor_release(x_423, 2);
 lean_ctor_release(x_423, 3);
 x_439 = x_423;
} else {
 lean_dec_ref(x_423);
 x_439 = lean_box(0);
}
x_440 = 1;
lean_inc(x_378);
if (lean_is_scalar(x_439)) {
 x_441 = lean_alloc_ctor(1, 4, 1);
} else {
 x_441 = x_439;
}
lean_ctor_set(x_441, 0, x_365);
lean_ctor_set(x_441, 1, x_366);
lean_ctor_set(x_441, 2, x_367);
lean_ctor_set(x_441, 3, x_378);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_442 = x_378;
} else {
 lean_dec_ref(x_378);
 x_442 = lean_box(0);
}
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_440);
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_435);
lean_ctor_set(x_443, 1, x_436);
lean_ctor_set(x_443, 2, x_437);
lean_ctor_set(x_443, 3, x_438);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_440);
x_444 = 0;
if (lean_is_scalar(x_434)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_434;
}
lean_ctor_set(x_445, 0, x_441);
lean_ctor_set(x_445, 1, x_432);
lean_ctor_set(x_445, 2, x_433);
lean_ctor_set(x_445, 3, x_443);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_444);
return x_445;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; uint8_t x_457; lean_object* x_458; 
x_446 = lean_ctor_get(x_377, 1);
lean_inc(x_446);
x_447 = lean_ctor_get(x_377, 2);
lean_inc(x_447);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_448 = x_377;
} else {
 lean_dec_ref(x_377);
 x_448 = lean_box(0);
}
x_449 = lean_ctor_get(x_378, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_378, 1);
lean_inc(x_450);
x_451 = lean_ctor_get(x_378, 2);
lean_inc(x_451);
x_452 = lean_ctor_get(x_378, 3);
lean_inc(x_452);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_453 = x_378;
} else {
 lean_dec_ref(x_378);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 4, 1);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_449);
lean_ctor_set(x_454, 1, x_450);
lean_ctor_set(x_454, 2, x_451);
lean_ctor_set(x_454, 3, x_452);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_431);
x_455 = 0;
if (lean_is_scalar(x_448)) {
 x_456 = lean_alloc_ctor(1, 4, 1);
} else {
 x_456 = x_448;
}
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_446);
lean_ctor_set(x_456, 2, x_447);
lean_ctor_set(x_456, 3, x_423);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_455);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_365);
lean_ctor_set(x_458, 1, x_366);
lean_ctor_set(x_458, 2, x_367);
lean_ctor_set(x_458, 3, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
}
}
}
}
}
}
else
{
uint8_t x_459; 
x_459 = l_Std_RBNode_isRed___rarg(x_365);
if (x_459 == 0)
{
lean_object* x_460; uint8_t x_461; lean_object* x_462; 
x_460 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_365, x_2, x_3);
x_461 = 1;
x_462 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_366);
lean_ctor_set(x_462, 2, x_367);
lean_ctor_set(x_462, 3, x_368);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
return x_462;
}
else
{
lean_object* x_463; lean_object* x_464; 
x_463 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_365, x_2, x_3);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; 
x_465 = lean_ctor_get(x_463, 3);
lean_inc(x_465);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; lean_object* x_470; uint8_t x_471; lean_object* x_472; 
x_466 = lean_ctor_get(x_463, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_463, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_468 = x_463;
} else {
 lean_dec_ref(x_463);
 x_468 = lean_box(0);
}
x_469 = 0;
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(1, 4, 1);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_465);
lean_ctor_set(x_470, 1, x_466);
lean_ctor_set(x_470, 2, x_467);
lean_ctor_set(x_470, 3, x_465);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_469);
x_471 = 1;
x_472 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_366);
lean_ctor_set(x_472, 2, x_367);
lean_ctor_set(x_472, 3, x_368);
lean_ctor_set_uint8(x_472, sizeof(void*)*4, x_471);
return x_472;
}
else
{
uint8_t x_473; 
x_473 = lean_ctor_get_uint8(x_465, sizeof(void*)*4);
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; 
x_474 = lean_ctor_get(x_463, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_463, 2);
lean_inc(x_475);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_476 = x_463;
} else {
 lean_dec_ref(x_463);
 x_476 = lean_box(0);
}
x_477 = lean_ctor_get(x_465, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_465, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_465, 2);
lean_inc(x_479);
x_480 = lean_ctor_get(x_465, 3);
lean_inc(x_480);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 lean_ctor_release(x_465, 2);
 lean_ctor_release(x_465, 3);
 x_481 = x_465;
} else {
 lean_dec_ref(x_465);
 x_481 = lean_box(0);
}
x_482 = 1;
if (lean_is_scalar(x_481)) {
 x_483 = lean_alloc_ctor(1, 4, 1);
} else {
 x_483 = x_481;
}
lean_ctor_set(x_483, 0, x_464);
lean_ctor_set(x_483, 1, x_474);
lean_ctor_set(x_483, 2, x_475);
lean_ctor_set(x_483, 3, x_477);
lean_ctor_set_uint8(x_483, sizeof(void*)*4, x_482);
if (lean_is_scalar(x_476)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_476;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_366);
lean_ctor_set(x_484, 2, x_367);
lean_ctor_set(x_484, 3, x_368);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_482);
x_485 = 0;
x_486 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_478);
lean_ctor_set(x_486, 2, x_479);
lean_ctor_set(x_486, 3, x_484);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_485);
return x_486;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; lean_object* x_491; uint8_t x_492; lean_object* x_493; 
x_487 = lean_ctor_get(x_463, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_463, 2);
lean_inc(x_488);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_489 = x_463;
} else {
 lean_dec_ref(x_463);
 x_489 = lean_box(0);
}
x_490 = 0;
if (lean_is_scalar(x_489)) {
 x_491 = lean_alloc_ctor(1, 4, 1);
} else {
 x_491 = x_489;
}
lean_ctor_set(x_491, 0, x_464);
lean_ctor_set(x_491, 1, x_487);
lean_ctor_set(x_491, 2, x_488);
lean_ctor_set(x_491, 3, x_465);
lean_ctor_set_uint8(x_491, sizeof(void*)*4, x_490);
x_492 = 1;
x_493 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_366);
lean_ctor_set(x_493, 2, x_367);
lean_ctor_set(x_493, 3, x_368);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_492);
return x_493;
}
}
}
else
{
uint8_t x_494; 
x_494 = lean_ctor_get_uint8(x_464, sizeof(void*)*4);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; lean_object* x_508; 
x_495 = lean_ctor_get(x_463, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_463, 2);
lean_inc(x_496);
x_497 = lean_ctor_get(x_463, 3);
lean_inc(x_497);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_498 = x_463;
} else {
 lean_dec_ref(x_463);
 x_498 = lean_box(0);
}
x_499 = lean_ctor_get(x_464, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_464, 1);
lean_inc(x_500);
x_501 = lean_ctor_get(x_464, 2);
lean_inc(x_501);
x_502 = lean_ctor_get(x_464, 3);
lean_inc(x_502);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_503 = x_464;
} else {
 lean_dec_ref(x_464);
 x_503 = lean_box(0);
}
x_504 = 1;
if (lean_is_scalar(x_503)) {
 x_505 = lean_alloc_ctor(1, 4, 1);
} else {
 x_505 = x_503;
}
lean_ctor_set(x_505, 0, x_499);
lean_ctor_set(x_505, 1, x_500);
lean_ctor_set(x_505, 2, x_501);
lean_ctor_set(x_505, 3, x_502);
lean_ctor_set_uint8(x_505, sizeof(void*)*4, x_504);
if (lean_is_scalar(x_498)) {
 x_506 = lean_alloc_ctor(1, 4, 1);
} else {
 x_506 = x_498;
}
lean_ctor_set(x_506, 0, x_497);
lean_ctor_set(x_506, 1, x_366);
lean_ctor_set(x_506, 2, x_367);
lean_ctor_set(x_506, 3, x_368);
lean_ctor_set_uint8(x_506, sizeof(void*)*4, x_504);
x_507 = 0;
x_508 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_495);
lean_ctor_set(x_508, 2, x_496);
lean_ctor_set(x_508, 3, x_506);
lean_ctor_set_uint8(x_508, sizeof(void*)*4, x_507);
return x_508;
}
else
{
lean_object* x_509; 
x_509 = lean_ctor_get(x_463, 3);
lean_inc(x_509);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; lean_object* x_514; uint8_t x_515; lean_object* x_516; 
x_510 = lean_ctor_get(x_463, 1);
lean_inc(x_510);
x_511 = lean_ctor_get(x_463, 2);
lean_inc(x_511);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_512 = x_463;
} else {
 lean_dec_ref(x_463);
 x_512 = lean_box(0);
}
x_513 = 0;
if (lean_is_scalar(x_512)) {
 x_514 = lean_alloc_ctor(1, 4, 1);
} else {
 x_514 = x_512;
}
lean_ctor_set(x_514, 0, x_464);
lean_ctor_set(x_514, 1, x_510);
lean_ctor_set(x_514, 2, x_511);
lean_ctor_set(x_514, 3, x_509);
lean_ctor_set_uint8(x_514, sizeof(void*)*4, x_513);
x_515 = 1;
x_516 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_366);
lean_ctor_set(x_516, 2, x_367);
lean_ctor_set(x_516, 3, x_368);
lean_ctor_set_uint8(x_516, sizeof(void*)*4, x_515);
return x_516;
}
else
{
uint8_t x_517; 
x_517 = lean_ctor_get_uint8(x_509, sizeof(void*)*4);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; uint8_t x_530; lean_object* x_531; 
x_518 = lean_ctor_get(x_463, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_463, 2);
lean_inc(x_519);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_520 = x_463;
} else {
 lean_dec_ref(x_463);
 x_520 = lean_box(0);
}
x_521 = lean_ctor_get(x_509, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_509, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_509, 2);
lean_inc(x_523);
x_524 = lean_ctor_get(x_509, 3);
lean_inc(x_524);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 lean_ctor_release(x_509, 2);
 lean_ctor_release(x_509, 3);
 x_525 = x_509;
} else {
 lean_dec_ref(x_509);
 x_525 = lean_box(0);
}
x_526 = 1;
lean_inc(x_464);
if (lean_is_scalar(x_525)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_525;
}
lean_ctor_set(x_527, 0, x_464);
lean_ctor_set(x_527, 1, x_518);
lean_ctor_set(x_527, 2, x_519);
lean_ctor_set(x_527, 3, x_521);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_528 = x_464;
} else {
 lean_dec_ref(x_464);
 x_528 = lean_box(0);
}
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(1, 4, 1);
} else {
 x_529 = x_528;
}
lean_ctor_set(x_529, 0, x_524);
lean_ctor_set(x_529, 1, x_366);
lean_ctor_set(x_529, 2, x_367);
lean_ctor_set(x_529, 3, x_368);
lean_ctor_set_uint8(x_529, sizeof(void*)*4, x_526);
x_530 = 0;
if (lean_is_scalar(x_520)) {
 x_531 = lean_alloc_ctor(1, 4, 1);
} else {
 x_531 = x_520;
}
lean_ctor_set(x_531, 0, x_527);
lean_ctor_set(x_531, 1, x_522);
lean_ctor_set(x_531, 2, x_523);
lean_ctor_set(x_531, 3, x_529);
lean_ctor_set_uint8(x_531, sizeof(void*)*4, x_530);
return x_531;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; uint8_t x_543; lean_object* x_544; 
x_532 = lean_ctor_get(x_463, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_463, 2);
lean_inc(x_533);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_534 = x_463;
} else {
 lean_dec_ref(x_463);
 x_534 = lean_box(0);
}
x_535 = lean_ctor_get(x_464, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_464, 1);
lean_inc(x_536);
x_537 = lean_ctor_get(x_464, 2);
lean_inc(x_537);
x_538 = lean_ctor_get(x_464, 3);
lean_inc(x_538);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_539 = x_464;
} else {
 lean_dec_ref(x_464);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 4, 1);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_535);
lean_ctor_set(x_540, 1, x_536);
lean_ctor_set(x_540, 2, x_537);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_517);
x_541 = 0;
if (lean_is_scalar(x_534)) {
 x_542 = lean_alloc_ctor(1, 4, 1);
} else {
 x_542 = x_534;
}
lean_ctor_set(x_542, 0, x_540);
lean_ctor_set(x_542, 1, x_532);
lean_ctor_set(x_542, 2, x_533);
lean_ctor_set(x_542, 3, x_509);
lean_ctor_set_uint8(x_542, sizeof(void*)*4, x_541);
x_543 = 1;
x_544 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_366);
lean_ctor_set(x_544, 2, x_367);
lean_ctor_set(x_544, 3, x_368);
lean_ctor_set_uint8(x_544, sizeof(void*)*4, x_543);
return x_544;
}
}
}
}
}
}
}
}
}
}
}
lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_1, x_2, x_3);
x_7 = l_Std_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
lean_object* l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_TokenMap_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg(x_1, x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg(x_1, x_2, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Parser_TokenMap_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_insert___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_TokenMap_instInhabitedTokenMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Lean_Parser_TokenMap_instEmptyCollectionTokenMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_PrattParsingTables_leadingTable___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_PrattParsingTables_leadingParsers___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_PrattParsingTables_trailingTable___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_PrattParsingTables_trailingParsers___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedPrattParsingTables___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedPrattParsingTables() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instInhabitedPrattParsingTables___closed__1;
return x_1;
}
}
static uint8_t _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_5915__match__1___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_box(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_3);
x_10 = lean_box(x_1);
x_11 = lean_box(x_2);
x_12 = lean_apply_2(x_6, x_10, x_11);
return x_12;
}
}
case 1:
{
lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
x_13 = lean_box(x_2);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_14 = lean_box(0);
x_15 = lean_apply_1(x_4, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_4);
x_16 = lean_box(x_1);
x_17 = lean_box(x_2);
x_18 = lean_apply_2(x_6, x_16, x_17);
return x_18;
}
}
default: 
{
lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_box(x_2);
if (lean_obj_tag(x_19) == 2)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
x_20 = lean_box(0);
x_21 = lean_apply_1(x_5, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_5);
x_22 = lean_box(x_1);
x_23 = lean_box(x_2);
x_24 = lean_apply_2(x_6, x_22, x_23);
return x_24;
}
}
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_5915__match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_5915__match__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_5915__match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_5915__match__1___rarg(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_5915_(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; 
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
case 1:
{
lean_object* x_6; 
x_6 = lean_box(x_2);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 0;
return x_8;
}
}
default: 
{
lean_object* x_9; 
x_9 = lean_box(x_2);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = 0;
return x_11;
}
}
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_5915____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_5915_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_instBEqLeadingIdentBehavior___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_5915____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instBEqLeadingIdentBehavior() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instBEqLeadingIdentBehavior___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_instInhabitedPrattParsingTables___closed__1;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instInhabitedParserCategory___closed__1;
return x_1;
}
}
lean_object* l_Lean_Parser_indexed_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_indexed_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_indexed_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Parser_indexed_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_indexed_match__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_indexed_match__2___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Parser_indexed_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_indexed_match__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_indexed_match__3___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Parser_indexed_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_indexed_match__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_indexed_match__4___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Parser_indexed_match__5___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_1) {
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
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_Parser_indexed_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_indexed_match__5___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_indexed_match__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Parser_indexed_match__5___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Parser_indexed_match__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_apply_1(x_5, x_1);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_apply_1(x_5, x_1);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_2(x_4, x_9, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_apply_2(x_2, x_12, x_13);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 3);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_apply_4(x_3, x_15, x_16, x_17, x_18);
return x_19;
}
}
}
}
}
lean_object* l_Lean_Parser_indexed_match__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_indexed_match__6___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_indexed_match__7___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Parser_indexed_match__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_indexed_match__7___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
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
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
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
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
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
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
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
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
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
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
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
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
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
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
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
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_indexed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parser_peekToken(x_2, x_3);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 1);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 1, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
switch (lean_obj_tag(x_13)) {
case 0:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 1);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_5, 1, x_16);
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
case 1:
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_5);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_5, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg(x_1, x_22);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_box(0);
lean_ctor_set(x_5, 1, x_24);
return x_5;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
lean_ctor_set(x_5, 1, x_25);
return x_5;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
lean_dec(x_13);
x_28 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg(x_1, x_27);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
case 2:
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_5);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_5, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_dec(x_13);
x_36 = lean_box(0);
x_37 = lean_name_mk_string(x_36, x_35);
x_38 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg(x_1, x_37);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_box(0);
lean_ctor_set(x_5, 1, x_39);
return x_5;
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
lean_ctor_set(x_5, 1, x_40);
return x_5;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_5, 0);
lean_inc(x_41);
lean_dec(x_5);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_dec(x_13);
x_43 = lean_box(0);
x_44 = lean_name_mk_string(x_43, x_42);
x_45 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg(x_1, x_44);
lean_dec(x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
default: 
{
switch (x_4) {
case 0:
{
uint8_t x_50; 
lean_dec(x_13);
x_50 = !lean_is_exclusive(x_5);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_5, 1);
lean_dec(x_51);
x_52 = l_Lean_identKind;
x_53 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg(x_1, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_box(0);
lean_ctor_set(x_5, 1, x_54);
return x_5;
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
lean_ctor_set(x_5, 1, x_55);
return x_5;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_5, 0);
lean_inc(x_56);
lean_dec(x_5);
x_57 = l_Lean_identKind;
x_58 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg(x_1, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
case 1:
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_5);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_5, 1);
lean_dec(x_64);
x_65 = lean_ctor_get(x_13, 2);
lean_inc(x_65);
lean_dec(x_13);
x_66 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg(x_1, x_65);
lean_dec(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Lean_identKind;
x_68 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg(x_1, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_box(0);
lean_ctor_set(x_5, 1, x_69);
return x_5;
}
else
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
lean_ctor_set(x_5, 1, x_70);
return x_5;
}
}
else
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
lean_dec(x_66);
lean_ctor_set(x_5, 1, x_71);
return x_5;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_5, 0);
lean_inc(x_72);
lean_dec(x_5);
x_73 = lean_ctor_get(x_13, 2);
lean_inc(x_73);
lean_dec(x_13);
x_74 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg(x_1, x_73);
lean_dec(x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = l_Lean_identKind;
x_76 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg(x_1, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_72);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_74, 0);
lean_inc(x_81);
lean_dec(x_74);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
default: 
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_5);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_5, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_13, 2);
lean_inc(x_85);
lean_dec(x_13);
x_86 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg(x_1, x_85);
lean_dec(x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = l_Lean_identKind;
x_88 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg(x_1, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_box(0);
lean_ctor_set(x_5, 1, x_89);
return x_5;
}
else
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
lean_dec(x_88);
lean_ctor_set(x_5, 1, x_90);
return x_5;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_86, 0);
lean_inc(x_91);
lean_dec(x_86);
x_92 = l_Lean_identKind;
x_93 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg(x_1, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_ctor_set(x_5, 1, x_91);
return x_5;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec(x_93);
x_95 = l_List_append___rarg(x_91, x_94);
lean_ctor_set(x_5, 1, x_95);
return x_5;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_5, 0);
lean_inc(x_96);
lean_dec(x_5);
x_97 = lean_ctor_get(x_13, 2);
lean_inc(x_97);
lean_dec(x_13);
x_98 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg(x_1, x_97);
lean_dec(x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Lean_identKind;
x_100 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg(x_1, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_96);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_100, 0);
lean_inc(x_103);
lean_dec(x_100);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_96);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_98, 0);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Lean_identKind;
x_107 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg(x_1, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_96);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_List_append___rarg(x_105, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_96);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
}
}
}
}
}
}
lean_object* l_Lean_Parser_indexed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_indexed___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_indexed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_indexed___rarg(x_1, x_2, x_3, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_IO_mkRef___at_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6172____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_mk_ref(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6172____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_whitespace(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6172____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6172____lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6172_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6172____closed__1;
x_3 = l_IO_mkRef___at_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6172____spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6172____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6172____lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6190____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Parser_categoryParserFnRef;
x_3 = lean_st_ref_get(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6190____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6190____lambda__1), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6190_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6190____closed__1;
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_categoryParserFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Parser_categoryParserFnExtension;
x_7 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_6, x_5);
lean_dec(x_5);
x_8 = lean_apply_3(x_7, x_1, x_2, x_3);
return x_8;
}
}
lean_object* l_Lean_Parser_categoryParser___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_ctor_set(x_3, 2, x_2);
x_11 = l_Lean_Parser_categoryParserFn(x_1, x_3, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
x_14 = lean_ctor_get(x_7, 2);
x_15 = lean_ctor_get(x_7, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 1, x_16);
x_17 = l_Lean_Parser_categoryParserFn(x_1, x_3, x_4);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_7, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_7, 3);
lean_inc(x_25);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 x_26 = x_7;
} else {
 lean_dec_ref(x_7);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(0, 4, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 1, x_27);
lean_ctor_set(x_3, 0, x_21);
x_28 = l_Lean_Parser_categoryParserFn(x_1, x_3, x_4);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_ctor_get(x_3, 1);
x_31 = lean_ctor_get(x_3, 3);
x_32 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_33 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_34 = lean_ctor_get(x_3, 4);
x_35 = lean_ctor_get(x_3, 5);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_3);
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_29, 2);
lean_inc(x_38);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 x_39 = x_29;
} else {
 lean_dec_ref(x_29);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 3, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_38);
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_30, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_30, 3);
lean_inc(x_44);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 lean_ctor_release(x_30, 3);
 x_45 = x_30;
} else {
 lean_dec_ref(x_30);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 4, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_43);
lean_ctor_set(x_46, 3, x_44);
x_47 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_2);
lean_ctor_set(x_47, 3, x_31);
lean_ctor_set(x_47, 4, x_34);
lean_ctor_set(x_47, 5, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*6, x_32);
lean_ctor_set_uint8(x_47, sizeof(void*)*6 + 1, x_33);
x_48 = l_Lean_Parser_categoryParserFn(x_1, x_47, x_4);
return x_48;
}
}
}
lean_object* l_Lean_Parser_categoryParser(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_categoryParser___elambda__1), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = l_Lean_Parser_errorAtSavedPos___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_termParser(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_term___u2218_____closed__6;
x_3 = l_Lean_Parser_categoryParser(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_checkNoImmediateColon___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected ':'");
return x_1;
}
}
lean_object* l_Lean_Parser_checkNoImmediateColon___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_3);
lean_dec(x_3);
x_5 = l_Lean_Parser_checkTailNoWs(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_string_utf8_at_end(x_7, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_10 = lean_string_utf8_get(x_7, x_8);
lean_dec(x_8);
x_11 = 58;
x_12 = x_10 == x_11;
if (x_12 == 0)
{
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Parser_checkNoImmediateColon___elambda__1___closed__1;
x_14 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_13);
return x_14;
}
}
else
{
lean_dec(x_8);
return x_2;
}
}
}
}
static lean_object* _init_l_Lean_Parser_checkNoImmediateColon___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_checkNoImmediateColon___elambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_checkNoImmediateColon___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_errorAtSavedPos___closed__1;
x_2 = l_Lean_Parser_checkNoImmediateColon___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_checkNoImmediateColon() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_checkNoImmediateColon___closed__2;
return x_1;
}
}
lean_object* l_Lean_Parser_checkNoImmediateColon___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_checkNoImmediateColon___elambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_setExpectedFn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_apply_1(x_3, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_apply_5(x_2, x_1, x_9, x_6, x_7, x_8);
return x_10;
}
}
}
lean_object* l_Lean_Parser_setExpectedFn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_setExpectedFn_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_setExpectedFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
return x_4;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_4, 3);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_8, 1, x_12);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_5, 0, x_15);
return x_4;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_4, 2);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_21 = x_16;
} else {
 lean_dec_ref(x_16);
 x_21 = lean_box(0);
}
x_22 = lean_box(0);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_5, 0, x_23);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_5);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_5, 0);
lean_inc(x_25);
lean_dec(x_5);
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_4, 2);
lean_inc(x_28);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_29 = x_4;
} else {
 lean_dec_ref(x_4);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_31 = x_25;
} else {
 lean_dec_ref(x_25);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
if (lean_is_scalar(x_29)) {
 x_35 = lean_alloc_ctor(0, 4, 0);
} else {
 x_35 = x_29;
}
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_27);
lean_ctor_set(x_35, 2, x_28);
lean_ctor_set(x_35, 3, x_34);
return x_35;
}
}
}
}
lean_object* l_Lean_Parser_setExpectedFn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_setExpectedFn___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_setExpectedFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_setExpectedFn(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_setExpected___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_setExpectedFn___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_setExpected___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_setExpected___elambda__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_setExpected(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_setExpected___elambda__1___rarg), 3, 1);
lean_closure_set(x_5, 0, x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_setExpected___elambda__1___rarg), 3, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Parser_setExpected___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_setExpected___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_setExpected___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_setExpected(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_pushNone___elambda__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkOptionalNode___closed__1;
x_3 = l_Lean_Parser_ParserState_pushSyntax(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_pushNone___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_pushNone___elambda__1___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_pushNone___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_pushNone___elambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_pushNone___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_errorAtSavedPos___closed__1;
x_2 = l_Lean_Parser_pushNone___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_pushNone() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_pushNone___closed__2;
return x_1;
}
}
lean_object* l_Lean_Parser_pushNone___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_pushNone___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_prec_x28___x29___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_term___u2218_____closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_categoryParser___elambda__1), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_prec_x28___x29___closed__7;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_quote___closed__1;
x_2 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__4;
x_2 = l_Char_quote___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Char_quote___closed__1;
x_2 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__6;
x_2 = l_Char_quote___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__1;
x_6 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__5;
lean_inc(x_1);
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = l_Lean_Syntax_mkAntiquotNode___closed__6;
x_12 = l_Lean_Parser_ParserState_mkNode(x_7, x_11, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__2;
lean_inc(x_1);
x_14 = l_Lean_Parser_toggleInsideQuotFn(x_13, x_1, x_7);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
x_16 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_15, x_9);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = l_Lean_Syntax_mkAntiquotNode___closed__6;
x_18 = l_Lean_Parser_ParserState_mkNode(x_14, x_17, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__3;
x_20 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__7;
x_21 = l_Lean_Parser_symbolFnAux(x_19, x_20, x_1, x_14);
x_22 = l_Lean_Syntax_mkAntiquotNode___closed__6;
x_23 = l_Lean_Parser_ParserState_mkNode(x_21, x_22, x_4);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__1;
x_2 = l_Lean_Parser_symbolInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_term___u2218_____closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Parser_categoryParser(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__3;
x_2 = l_Lean_Parser_symbolInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_antiquotNestedExpr___closed__2;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_antiquotNestedExpr___closed__3;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr___closed__1;
x_2 = l_Lean_Parser_antiquotNestedExpr___closed__4;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_mkAntiquotNode___closed__6;
x_2 = l_Lean_Parser_antiquotNestedExpr___closed__5;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotNestedExpr___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr___closed__6;
x_2 = l_Lean_Parser_antiquotNestedExpr___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_antiquotNestedExpr___closed__8;
return x_1;
}
}
lean_object* l_Lean_Parser_antiquotExpr___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = l_Lean_Parser_identNoAntiquot___closed__2;
x_4 = l_Lean_Parser_antiquotNestedExpr___closed__7;
x_5 = 1;
x_6 = l_Lean_Parser_orelseFnCore(x_3, x_4, x_5, x_1, x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_antiquotNestedExpr;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_identNoAntiquot___closed__1;
x_4 = l_Lean_Parser_orelseInfo(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_antiquotExpr___elambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotExpr___closed__1;
x_2 = l_Lean_Parser_antiquotExpr___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_antiquotExpr___closed__3;
return x_1;
}
}
lean_object* l_Lean_Parser_mkAntiquot___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = l_Lean_Parser_maxPrec;
x_5 = l_Lean_Parser_checkPrecFn(x_4, x_2, x_3);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_9; 
x_9 = lean_apply_2(x_1, x_2, x_5);
return x_9;
}
}
}
lean_object* l_Lean_Parser_mkAntiquot___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = l_Lean_Parser_maxPrec;
x_5 = l_Lean_Parser_checkPrecFn(x_4, x_2, x_3);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_9; 
x_9 = lean_apply_2(x_1, x_2, x_5);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no space before ':");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_myMacro____x40_Init_Notation___hyg_12721____closed__9;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot___closed__2;
x_2 = l_Lean_Parser_symbolInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term___x24_______closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot___closed__5;
x_2 = l_Lean_Parser_symbolInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_mkAntiquot___closed__6;
x_2 = l_Lean_Parser_mkAntiquot___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_mkAntiquot___closed__8;
x_3 = l_Lean_Parser_setExpected(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_mkAntiquot___closed__6;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedParserDescr___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkNoWsBefore___elambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_mkAntiquot___closed__11;
x_2 = l_Lean_Parser_mkAntiquot___closed__7;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot___closed__10;
x_2 = l_Lean_Parser_noFirstTokenInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot___closed__12;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_manyFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no space before spliced term");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot___closed__15;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkNoWsBefore___elambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_checkNoImmediateColon;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_pushNone;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_andthenInfo(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_checkNoImmediateColon___closed__1;
x_2 = l_Lean_Parser_pushNone___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_mkAntiquot(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_4 = l_Lean_Parser_mkAntiquot___closed__1;
x_5 = lean_string_append(x_4, x_1);
x_6 = l_Char_quote___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_String_trim(x_1);
x_9 = 0;
lean_inc(x_8);
x_10 = l_Lean_Parser_nonReservedSymbolInfo(x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolFn), 3, 1);
lean_closure_set(x_11, 0, x_8);
x_12 = l_Lean_Parser_mkAntiquot___closed__3;
x_13 = l_Lean_Parser_andthenInfo(x_12, x_10);
x_14 = l_Lean_Parser_mkAntiquot___closed__4;
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_11);
x_16 = l_Lean_Parser_epsilonInfo;
x_17 = l_Lean_Parser_andthenInfo(x_16, x_13);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_checkNoWsBefore___elambda__1___boxed), 3, 1);
lean_closure_set(x_18, 0, x_7);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_15);
x_20 = l_Lean_Syntax_mkAntiquotNode___closed__12;
x_21 = l_Lean_Parser_nodeInfo(x_20, x_17);
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_19);
x_23 = l_Lean_Parser_antiquotExpr;
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = l_Lean_Parser_mkAntiquot___closed__9;
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_73; 
x_73 = lean_box(0);
x_27 = x_73;
goto block_72;
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_2, 0);
lean_inc(x_74);
lean_dec(x_2);
x_27 = x_74;
goto block_72;
}
block_72:
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_Syntax_mkAntiquotNode___closed__2;
x_29 = l_Lean_Name_append(x_27, x_28);
lean_dec(x_27);
if (x_3 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_30 = l_Lean_Parser_andthenInfo(x_24, x_21);
x_31 = l_Lean_Parser_antiquotExpr___closed__2;
x_32 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_32, 0, x_31);
lean_closure_set(x_32, 1, x_22);
x_33 = l_Lean_Parser_andthenInfo(x_16, x_30);
x_34 = l_Lean_Parser_mkAntiquot___closed__16;
x_35 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_35, 0, x_34);
lean_closure_set(x_35, 1, x_32);
x_36 = l_Lean_Parser_mkAntiquot___closed__13;
x_37 = l_Lean_Parser_andthenInfo(x_36, x_33);
x_38 = l_Lean_Parser_mkAntiquot___closed__14;
x_39 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_39, 0, x_38);
lean_closure_set(x_39, 1, x_35);
x_40 = l_Lean_Parser_mkAntiquot___closed__6;
x_41 = l_Lean_Parser_andthenInfo(x_40, x_37);
x_42 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_42, 0, x_26);
lean_closure_set(x_42, 1, x_39);
x_43 = lean_alloc_closure((void*)(l_Lean_Parser_atomicFn), 3, 1);
lean_closure_set(x_43, 0, x_42);
lean_inc(x_29);
x_44 = l_Lean_Parser_nodeInfo(x_29, x_41);
x_45 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_45, 0, x_29);
lean_closure_set(x_45, 1, x_43);
x_46 = l_Lean_Parser_andthenInfo(x_16, x_44);
x_47 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot___elambda__1), 3, 1);
lean_closure_set(x_47, 0, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_49 = l_Lean_Parser_mkAntiquot___closed__17;
x_50 = l_Lean_Parser_orelseInfo(x_21, x_49);
x_51 = l_Lean_Parser_mkAntiquot___closed__18;
x_52 = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn), 4, 2);
lean_closure_set(x_52, 0, x_22);
lean_closure_set(x_52, 1, x_51);
x_53 = l_Lean_Parser_andthenInfo(x_24, x_50);
x_54 = l_Lean_Parser_antiquotExpr___closed__2;
x_55 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_55, 0, x_54);
lean_closure_set(x_55, 1, x_52);
x_56 = l_Lean_Parser_andthenInfo(x_16, x_53);
x_57 = l_Lean_Parser_mkAntiquot___closed__16;
x_58 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_58, 0, x_57);
lean_closure_set(x_58, 1, x_55);
x_59 = l_Lean_Parser_mkAntiquot___closed__13;
x_60 = l_Lean_Parser_andthenInfo(x_59, x_56);
x_61 = l_Lean_Parser_mkAntiquot___closed__14;
x_62 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_62, 0, x_61);
lean_closure_set(x_62, 1, x_58);
x_63 = l_Lean_Parser_mkAntiquot___closed__6;
x_64 = l_Lean_Parser_andthenInfo(x_63, x_60);
x_65 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_65, 0, x_26);
lean_closure_set(x_65, 1, x_62);
x_66 = lean_alloc_closure((void*)(l_Lean_Parser_atomicFn), 3, 1);
lean_closure_set(x_66, 0, x_65);
lean_inc(x_29);
x_67 = l_Lean_Parser_nodeInfo(x_29, x_64);
x_68 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_68, 0, x_29);
lean_closure_set(x_68, 1, x_66);
x_69 = l_Lean_Parser_andthenInfo(x_16, x_67);
x_70 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot___elambda__2), 3, 1);
lean_closure_set(x_70, 0, x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
lean_object* l_Lean_Parser_mkAntiquot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Parser_tryAnti_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 2)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_apply_3(x_2, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
}
lean_object* l_Lean_Parser_tryAnti_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_tryAnti_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_tryAnti_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Parser_tryAnti_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_tryAnti_match__2___rarg), 2, 0);
return x_2;
}
}
uint8_t l_Lean_Parser_tryAnti(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_peekToken(x_1, x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
if (lean_obj_tag(x_6) == 2)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_term___x24_______closed__5;
x_9 = lean_string_dec_eq(x_7, x_8);
lean_dec(x_7);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_6);
x_10 = 0;
return x_10;
}
}
}
}
lean_object* l_Lean_Parser_tryAnti___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_tryAnti(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_withAntiquotFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_inc(x_4);
lean_inc(x_3);
x_5 = l_Lean_Parser_tryAnti(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_3, x_4);
return x_6;
}
else
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
x_8 = l_Lean_Parser_orelseFnCore(x_1, x_2, x_7, x_3, x_4);
return x_8;
}
}
}
lean_object* l_Lean_Parser_withAntiquot(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_orelseInfo(x_3, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotFn), 4, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
lean_object* l_Lean_Parser_withoutInfo___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_withoutInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_withoutInfo___elambda__1), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_errorAtSavedPos___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Parser_mkAntiquotSplice___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = l_Lean_Parser_maxPrec;
x_5 = l_Lean_Parser_checkPrecFn(x_4, x_2, x_3);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_9; 
x_9 = lean_apply_2(x_1, x_2, x_5);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Syntax_antiquotSpliceKind_x3f_match__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term_x5b___x5d___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquotSplice___closed__2;
x_2 = l_Lean_Parser_symbolInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquotSplice___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term_x5b___x5d___closed__9;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquotSplice___closed__5;
x_2 = l_Lean_Parser_symbolInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquotSplice___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_mkAntiquotSplice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_4 = l_Lean_Parser_mkAntiquotSplice___closed__1;
x_5 = l_Lean_Name_append(x_1, x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = l_Lean_nullKind;
x_8 = l_Lean_Parser_nodeInfo(x_7, x_6);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = l_Lean_Parser_mkAntiquotSplice___closed__6;
x_13 = l_Lean_Parser_andthenInfo(x_12, x_11);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = l_Lean_Parser_mkAntiquotSplice___closed__7;
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
x_17 = l_Lean_Parser_andthenInfo(x_8, x_13);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_18, 0, x_10);
lean_closure_set(x_18, 1, x_16);
x_19 = l_Lean_Parser_mkAntiquotSplice___closed__3;
x_20 = l_Lean_Parser_andthenInfo(x_19, x_17);
x_21 = l_Lean_Parser_mkAntiquotSplice___closed__4;
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_18);
x_23 = l_Lean_Parser_epsilonInfo;
x_24 = l_Lean_Parser_andthenInfo(x_23, x_20);
x_25 = l_Lean_Parser_mkAntiquot___closed__16;
x_26 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_22);
x_27 = l_Lean_Parser_mkAntiquot___closed__13;
x_28 = l_Lean_Parser_andthenInfo(x_27, x_24);
x_29 = l_Lean_Parser_mkAntiquot___closed__14;
x_30 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_30, 0, x_29);
lean_closure_set(x_30, 1, x_26);
x_31 = l_Lean_Parser_mkAntiquot___closed__6;
x_32 = l_Lean_Parser_andthenInfo(x_31, x_28);
x_33 = l_Lean_Parser_mkAntiquot___closed__9;
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_35, 0, x_34);
lean_closure_set(x_35, 1, x_30);
x_36 = lean_alloc_closure((void*)(l_Lean_Parser_atomicFn), 3, 1);
lean_closure_set(x_36, 0, x_35);
lean_inc(x_5);
x_37 = l_Lean_Parser_nodeInfo(x_5, x_32);
x_38 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_38, 0, x_5);
lean_closure_set(x_38, 1, x_36);
x_39 = l_Lean_Parser_andthenInfo(x_23, x_37);
x_40 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquotSplice___elambda__1), 3, 1);
lean_closure_set(x_40, 0, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
lean_object* l_Lean_Parser_mkAntiquotSplice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_mkAntiquotSplice(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__1;
x_5 = l_Lean_Name_append(x_1, x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Parser_ParserState_mkNode(x_2, x_5, x_9);
return x_10;
}
}
lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_apply_2(x_2, x_3, x_1);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1(x_4, x_9, x_14);
return x_15;
}
}
}
lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_4);
x_6 = lean_apply_2(x_2, x_4, x_5);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_10);
lean_dec(x_10);
x_12 = l_Lean_Syntax_isAntiquot(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__2(x_6, x_3, x_4, x_1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_withAntiquotSuffixSpliceFn(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Parser_withAntiquotSuffixSplice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = l_Lean_Parser_andthenInfo(x_4, x_5);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSuffixSpliceFn___boxed), 5, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_inc(x_4);
lean_inc(x_3);
x_5 = l_Lean_Parser_tryAnti(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_2(x_1, x_3, x_4);
return x_6;
}
else
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
x_8 = l_Lean_Parser_orelseFnCore(x_2, x_1, x_7, x_3, x_4);
return x_8;
}
}
}
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_2);
x_4 = l_Lean_Parser_withoutInfo(x_2);
lean_inc(x_3);
x_5 = l_Lean_Parser_mkAntiquotSplice(x_1, x_4, x_3);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = l_Lean_Parser_andthenInfo(x_6, x_7);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSuffixSpliceFn___boxed), 5, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_10);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
x_13 = l_Lean_Parser_orelseInfo(x_12, x_8);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSpliceAndSuffix___elambda__1), 4, 2);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
lean_object* l_Lean_Parser_nodeWithAntiquot___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_inc(x_4);
lean_inc(x_3);
x_5 = l_Lean_Parser_tryAnti(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_2(x_1, x_3, x_4);
return x_6;
}
else
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
x_8 = l_Lean_Parser_orelseFnCore(x_2, x_1, x_7, x_3, x_4);
return x_8;
}
}
}
lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_2);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = l_Lean_Parser_mkAntiquot(x_1, x_5, x_4);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_inc(x_2);
x_8 = l_Lean_Parser_nodeInfo(x_2, x_7);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = l_Lean_Parser_orelseInfo(x_11, x_8);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_nodeWithAntiquot___elambda__1), 4, 2);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
lean_object* l_Lean_Parser_nodeWithAntiquot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_nodeWithAntiquot(x_1, x_2, x_3, x_5);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_sepByElemParser___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_myMacro____x40_Init_Notation___hyg_1202____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_sepByElemParser(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_String_trim(x_2);
x_4 = l_stx___x2a___closed__3;
x_5 = lean_string_append(x_3, x_4);
x_6 = l_String_trim(x_5);
lean_dec(x_5);
lean_inc(x_6);
x_7 = l_Lean_Parser_symbolInfo(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Parser_sepByElemParser___closed__1;
x_11 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_10, x_1, x_9);
return x_11;
}
}
lean_object* l_Lean_Parser_sepByElemParser___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_sepByElemParser(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_sepBy___elambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_sepByFn(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_sepBy(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l_Lean_Parser_sepByElemParser(x_1, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = l_Lean_Parser_sepByInfo(x_6, x_7);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_box(x_4);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy___elambda__1___boxed), 5, 3);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_9);
lean_closure_set(x_12, 2, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
lean_object* l_Lean_Parser_sepBy___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Parser_sepBy___elambda__1(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_sepBy___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_sepBy(x_1, x_2, x_3, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Parser_sepBy1___elambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_sepBy1Fn(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_sepBy1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l_Lean_Parser_sepByElemParser(x_1, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = l_Lean_Parser_sepBy1Info(x_6, x_7);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_box(x_4);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1___elambda__1___boxed), 5, 3);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_9);
lean_closure_set(x_12, 2, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
lean_object* l_Lean_Parser_sepBy1___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Parser_sepBy1___elambda__1(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_sepBy1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_sepBy1(x_1, x_2, x_3, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Parser_categoryParserOfStackFn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_categoryParserOfStackFn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserOfStackFn_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_categoryParserOfStackFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to determine parser category using syntax stack, the specified element on the stack is not an identifier");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_categoryParserOfStackFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to determine parser category using syntax stack, stack is too small");
return x_1;
}
}
lean_object* l_Lean_Parser_categoryParserOfStackFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_1, x_6);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_nat_sub(x_5, x_1);
lean_dec(x_5);
x_10 = lean_nat_sub(x_9, x_6);
lean_dec(x_9);
x_11 = l_Lean_instInhabitedSyntax;
x_12 = lean_array_get(x_11, x_4, x_10);
lean_dec(x_10);
lean_dec(x_4);
if (lean_obj_tag(x_12) == 3)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Parser_categoryParserFn(x_13, x_2, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_2);
x_15 = l_Lean_Parser_categoryParserOfStackFn___closed__1;
x_16 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_17 = l_Lean_Parser_categoryParserOfStackFn___closed__2;
x_18 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_17);
return x_18;
}
}
}
lean_object* l_Lean_Parser_categoryParserOfStackFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_categoryParserOfStackFn(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_categoryParserOfStack___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_ctor_set(x_3, 2, x_2);
x_11 = l_Lean_Parser_categoryParserOfStackFn(x_1, x_3, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
x_14 = lean_ctor_get(x_7, 2);
x_15 = lean_ctor_get(x_7, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 1, x_16);
x_17 = l_Lean_Parser_categoryParserOfStackFn(x_1, x_3, x_4);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_7, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_7, 3);
lean_inc(x_25);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 x_26 = x_7;
} else {
 lean_dec_ref(x_7);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(0, 4, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 1, x_27);
lean_ctor_set(x_3, 0, x_21);
x_28 = l_Lean_Parser_categoryParserOfStackFn(x_1, x_3, x_4);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_ctor_get(x_3, 1);
x_31 = lean_ctor_get(x_3, 3);
x_32 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_33 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_34 = lean_ctor_get(x_3, 4);
x_35 = lean_ctor_get(x_3, 5);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_3);
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_29, 2);
lean_inc(x_38);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 x_39 = x_29;
} else {
 lean_dec_ref(x_29);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 3, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_38);
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_30, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_30, 3);
lean_inc(x_44);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 lean_ctor_release(x_30, 3);
 x_45 = x_30;
} else {
 lean_dec_ref(x_30);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 4, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_43);
lean_ctor_set(x_46, 3, x_44);
x_47 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_2);
lean_ctor_set(x_47, 3, x_31);
lean_ctor_set(x_47, 4, x_34);
lean_ctor_set(x_47, 5, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*6, x_32);
lean_ctor_set_uint8(x_47, sizeof(void*)*6 + 1, x_33);
x_48 = l_Lean_Parser_categoryParserOfStackFn(x_1, x_47, x_4);
return x_48;
}
}
}
lean_object* l_Lean_Parser_categoryParserOfStack(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserOfStack___elambda__1___boxed), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = l_Lean_Parser_errorAtSavedPos___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_categoryParserOfStack___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_categoryParserOfStack___elambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Parser_evalParserConstUnsafe_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
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
lean_object* l_Lean_Parser_evalParserConstUnsafe_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_evalParserConstUnsafe___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__4;
x_2 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_evalParserConstUnsafe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TrailingParser");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_evalParserConstUnsafe___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__4;
x_2 = l_Lean_Parser_evalParserConstUnsafe___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_evalParserConstUnsafe___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("error running parser ");
return x_1;
}
}
lean_object* l_Lean_Parser_evalParserConstUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Parser_evalParserConstUnsafe___closed__1;
lean_inc(x_1);
lean_inc(x_5);
x_8 = l_Lean_Environment_evalConstCheck___rarg(x_5, x_6, x_7, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_8);
x_9 = l_Lean_Parser_evalParserConstUnsafe___closed__3;
lean_inc(x_1);
x_10 = l_Lean_Environment_evalConstCheck___rarg(x_5, x_6, x_9, x_1);
lean_dec(x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Name_toString___closed__1;
x_13 = l_Lean_Name_toStringWithSep(x_12, x_1);
x_14 = l_Lean_Parser_evalParserConstUnsafe___closed__4;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l___private_Init_Util_0__mkPanicMessage___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_11);
lean_dec(x_11);
x_19 = l_Lean_instInhabitedParserDescr___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_apply_2(x_23, x_2, x_3);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_apply_2(x_26, x_2, x_3);
return x_27;
}
}
}
lean_object* l_Lean_Parser_evalParserConst___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_evalParserConst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConst___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Parser_evalParserConst___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_evalParserConst___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_evalParserConst___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_evalParserConst(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_parserOfStackFnUnsafe_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_apply_3(x_3, x_6, x_11, x_12);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_3);
x_15 = lean_apply_1(x_4, x_1);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_apply_3(x_3, x_6, x_16, x_17);
return x_18;
}
}
}
}
}
lean_object* l_Lean_Parser_parserOfStackFnUnsafe_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFnUnsafe_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_parserOfStackFnUnsafe_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Parser_parserOfStackFnUnsafe_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFnUnsafe_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_parserOfStackFnUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to determine parser using syntax stack, the specified element on the stack is not an identifier");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_parserOfStackFnUnsafe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown parser ");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_parserOfStackFnUnsafe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected parser to return exactly one syntax object");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_parserOfStackFnUnsafe___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ambiguous parser name ");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_parserOfStackFnUnsafe___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to determine parser using syntax stack, stack is too small");
return x_1;
}
}
lean_object* l_Lean_Parser_parserOfStackFnUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_1, x_6);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_nat_sub(x_5, x_1);
x_10 = lean_nat_sub(x_9, x_6);
lean_dec(x_9);
x_11 = l_Lean_instInhabitedSyntax;
x_12 = lean_array_get(x_11, x_4, x_10);
lean_dec(x_10);
lean_dec(x_4);
if (lean_obj_tag(x_12) == 3)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_13);
lean_inc(x_2);
x_14 = l_Lean_Parser_ParserContext_resolveName(x_2, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_2);
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep(x_15, x_13);
x_17 = l_Lean_Parser_parserOfStackFnUnsafe___closed__2;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_instInhabitedParserDescr___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec(x_14);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_13);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Lean_Parser_evalParserConstUnsafe(x_25, x_2, x_3);
x_27 = lean_ctor_get(x_26, 3);
lean_inc(x_27);
x_28 = lean_box(0);
x_29 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_dec(x_5);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
x_31 = lean_array_get_size(x_30);
lean_dec(x_30);
x_32 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
x_33 = lean_nat_dec_eq(x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_Parser_parserOfStackFnUnsafe___closed__3;
x_35 = l_Lean_Parser_ParserState_mkUnexpectedError(x_26, x_34);
return x_35;
}
else
{
return x_26;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_2);
x_36 = l_Lean_Name_toString___closed__1;
x_37 = l_Lean_Name_toStringWithSep(x_36, x_13);
x_38 = l_Lean_Parser_parserOfStackFnUnsafe___closed__4;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = l_Lean_instInhabitedParserDescr___closed__1;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_41);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_2);
x_43 = lean_ctor_get(x_14, 1);
lean_inc(x_43);
lean_dec(x_14);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = l_Lean_Name_toString___closed__1;
x_45 = l_Lean_Name_toStringWithSep(x_44, x_13);
x_46 = l_Lean_Parser_parserOfStackFnUnsafe___closed__2;
x_47 = lean_string_append(x_46, x_45);
lean_dec(x_45);
x_48 = l_Lean_instInhabitedParserDescr___closed__1;
x_49 = lean_string_append(x_47, x_48);
x_50 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_43);
x_51 = l_Lean_Name_toString___closed__1;
x_52 = l_Lean_Name_toStringWithSep(x_51, x_13);
x_53 = l_Lean_Parser_parserOfStackFnUnsafe___closed__4;
x_54 = lean_string_append(x_53, x_52);
lean_dec(x_52);
x_55 = l_Lean_instInhabitedParserDescr___closed__1;
x_56 = lean_string_append(x_54, x_55);
x_57 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_2);
x_58 = l_Lean_Parser_parserOfStackFnUnsafe___closed__1;
x_59 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_60 = l_Lean_Parser_parserOfStackFnUnsafe___closed__5;
x_61 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_60);
return x_61;
}
}
}
lean_object* l_Lean_Parser_parserOfStackFnUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_parserOfStackFnUnsafe(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_parserOfStackFn___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Parser_parserOfStackFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Parser_parserOfStackFn___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_parserOfStackFn___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_parserOfStackFn(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Parser_parserOfStack___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_ctor_set(x_3, 2, x_2);
x_11 = l_Lean_Parser_parserOfStackFnUnsafe(x_1, x_3, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
x_14 = lean_ctor_get(x_7, 2);
x_15 = lean_ctor_get(x_7, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 1, x_16);
x_17 = l_Lean_Parser_parserOfStackFnUnsafe(x_1, x_3, x_4);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_7, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_7, 3);
lean_inc(x_25);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 x_26 = x_7;
} else {
 lean_dec_ref(x_7);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(0, 4, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 1, x_27);
lean_ctor_set(x_3, 0, x_21);
x_28 = l_Lean_Parser_parserOfStackFnUnsafe(x_1, x_3, x_4);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_ctor_get(x_3, 1);
x_31 = lean_ctor_get(x_3, 3);
x_32 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_33 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_34 = lean_ctor_get(x_3, 4);
x_35 = lean_ctor_get(x_3, 5);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_3);
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_29, 2);
lean_inc(x_38);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 x_39 = x_29;
} else {
 lean_dec_ref(x_29);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 3, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_38);
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_30, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_30, 3);
lean_inc(x_44);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 lean_ctor_release(x_30, 3);
 x_45 = x_30;
} else {
 lean_dec_ref(x_30);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 4, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_43);
lean_ctor_set(x_46, 3, x_44);
x_47 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_2);
lean_ctor_set(x_47, 3, x_31);
lean_ctor_set(x_47, 4, x_34);
lean_ctor_set(x_47, 5, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*6, x_32);
lean_ctor_set_uint8(x_47, sizeof(void*)*6 + 1, x_33);
x_48 = l_Lean_Parser_parserOfStackFnUnsafe(x_1, x_47, x_4);
return x_48;
}
}
}
lean_object* l_Lean_Parser_parserOfStack(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStack___elambda__1___boxed), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = l_Lean_Parser_errorAtSavedPos___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Parser_parserOfStack___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_parserOfStack___elambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Parser_evalInsideQuot___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_2(x_6, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Environment_contains(x_9, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_2(x_11, x_3, x_4);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_2);
x_13 = l_Lean_Parser_evalParserConstUnsafe(x_1, x_3, x_4);
return x_13;
}
}
}
}
lean_object* l_Lean_Parser_evalInsideQuot(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_evalInsideQuot___elambda__1), 4, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 1);
lean_dec(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_dec(x_7);
lean_ctor_set(x_2, 1, x_4);
return x_2;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_2, x_5);
x_7 = lean_nat_dec_eq(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_nullKind;
x_9 = l_Lean_Parser_ParserState_mkNode(x_1, x_8, x_2);
return x_9;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Lean_Parser_leadingParserAux_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Parser_leadingParserAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_leadingParserAux_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_leadingParserAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_inc(x_4);
x_9 = l_Lean_Parser_indexed___rarg(x_8, x_4, x_5, x_3);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_List_append___rarg(x_12, x_11);
x_14 = l_List_isEmpty___rarg(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = l_Lean_Parser_longestMatchFn(x_15, x_13, x_4, x_10);
x_17 = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(x_16, x_7);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_4);
x_18 = l_Lean_Name_toString___closed__1;
x_19 = l_Lean_Name_toStringWithSep(x_18, x_1);
x_20 = l_Lean_Parser_ParserState_mkError(x_10, x_19);
return x_20;
}
}
}
lean_object* l_Lean_Parser_leadingParserAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Parser_leadingParserAux(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Parser_leadingParser(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_box(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_leadingParserAux___boxed), 5, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_7);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Parser_tryAnti(x_5, x_6);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_4);
x_10 = l_Lean_Parser_leadingParserAux(x_1, x_2, x_3, x_5, x_6);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = 1;
x_12 = l_Lean_Parser_orelseFnCore(x_4, x_8, x_11, x_5, x_6);
return x_12;
}
}
}
lean_object* l_Lean_Parser_leadingParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Parser_leadingParser(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Parser_trailingLoopStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_List_append___rarg(x_3, x_7);
x_9 = l_Lean_Parser_longestMatchFn(x_6, x_8, x_4, x_5);
return x_9;
}
}
lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkTrailingResult(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_ParserState_popSyntax(x_3);
x_7 = l_Lean_Parser_ParserState_popSyntax(x_6);
x_8 = l_Lean_Parser_ParserState_pushSyntax(x_7, x_5);
return x_8;
}
}
lean_object* l_Lean_Parser_trailingLoop_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Parser_trailingLoop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_trailingLoop_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_trailingLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = 0;
lean_inc(x_2);
x_6 = l_Lean_Parser_indexed___rarg(x_4, x_2, x_3, x_5);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_List_isEmpty___rarg(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_10);
x_12 = lean_array_get_size(x_10);
lean_dec(x_10);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_Parser_trailingLoopStep(x_1, x_11, x_8, x_2, x_7);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
x_16 = lean_box(0);
x_17 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
x_19 = lean_nat_dec_eq(x_18, x_13);
lean_dec(x_18);
if (x_19 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
return x_14;
}
else
{
lean_object* x_20; 
x_20 = l_Lean_Parser_ParserState_restore(x_14, x_12, x_13);
lean_dec(x_12);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_13);
x_21 = l___private_Lean_Parser_Basic_0__Lean_Parser_mkTrailingResult(x_14, x_12);
x_3 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
x_24 = l_List_isEmpty___rarg(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
x_26 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_25);
x_27 = lean_array_get_size(x_25);
lean_dec(x_25);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Lean_Parser_trailingLoopStep(x_1, x_26, x_8, x_2, x_7);
x_30 = lean_ctor_get(x_29, 3);
lean_inc(x_30);
x_31 = lean_box(0);
x_32 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
x_34 = lean_nat_dec_eq(x_33, x_28);
lean_dec(x_33);
if (x_34 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
return x_29;
}
else
{
lean_object* x_35; 
x_35 = l_Lean_Parser_ParserState_restore(x_29, x_27, x_28);
lean_dec(x_27);
return x_35;
}
}
else
{
lean_object* x_36; 
lean_dec(x_28);
x_36 = l___private_Lean_Parser_Basic_0__Lean_Parser_mkTrailingResult(x_29, x_27);
x_3 = x_36;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
}
}
lean_object* l_Lean_Parser_prattParser(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_box(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_leadingParserAux___boxed), 5, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_7);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Parser_tryAnti(x_5, x_6);
x_10 = lean_box(0);
if (x_9 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_4);
lean_inc(x_5);
lean_inc(x_2);
x_11 = l_Lean_Parser_leadingParserAux(x_1, x_2, x_3, x_5, x_6);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
x_13 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_12, x_10);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Parser_trailingLoop(x_2, x_5, x_11);
return x_14;
}
}
else
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_1);
x_15 = 1;
lean_inc(x_5);
x_16 = l_Lean_Parser_orelseFnCore(x_4, x_8, x_15, x_5, x_6);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
x_18 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_649____at_Lean_Parser_ParserState_hasError___spec__1(x_17, x_10);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
return x_16;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_Parser_trailingLoop(x_2, x_5, x_16);
return x_19;
}
}
}
}
lean_object* l_Lean_Parser_prattParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Parser_prattParser(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdxFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("field index");
return x_1;
}
}
lean_object* l_Lean_Parser_fieldIdxFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_string_utf8_get(x_5, x_3);
x_7 = l_Char_isDigit(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Parser_fieldIdxFn___closed__1;
x_9 = l_Lean_Parser_ParserState_mkErrorAt(x_2, x_8, x_3);
return x_9;
}
else
{
uint32_t x_10; uint8_t x_11; 
x_10 = 48;
x_11 = x_6 == x_10;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1;
x_13 = l_Lean_Parser_takeWhileFn(x_12, x_1, x_2);
x_14 = l_Lean_fieldIdxKind;
x_15 = l_Lean_Parser_mkNodeToken(x_14, x_3, x_1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Parser_fieldIdxFn___closed__1;
x_17 = l_Lean_Parser_ParserState_mkErrorAt(x_2, x_16, x_3);
return x_17;
}
}
}
}
lean_object* l_Lean_Parser_fieldIdxFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_fieldIdxFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_fieldIdxKind___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_fieldIdxKind___closed__1;
x_2 = l_Lean_Parser_fieldIdx___closed__1;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_fieldIdxKind___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_fieldIdx___closed__2;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_fieldIdx___closed__3;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_fieldIdxFn___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_fieldIdx___closed__2;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lean_Parser_fieldIdx___closed__5;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotFn), 4, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_fieldIdx___closed__4;
x_2 = l_Lean_Parser_fieldIdx___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_fieldIdx___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_skip___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_instInhabitedParser___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_skip() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_skip___closed__1;
return x_1;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = x_1 + x_7;
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_4 == x_5;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
x_10 = lean_apply_2(x_2, x_9, x_6);
x_11 = lean_box_usize(x_4);
x_12 = lean_box_usize(x_5);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_6);
return x_17;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Lean_Syntax_foldArgsM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = l_Lean_Syntax_getArgs(x_2);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_4);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_6, x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_4);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg(x_1, x_3, x_5, x_16, x_17, x_4);
return x_18;
}
}
}
}
lean_object* l_Lean_Syntax_foldArgsM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_foldArgsM___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
lean_object* l_Lean_Syntax_foldArgsM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_foldArgsM___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_7, x_5);
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_foldArgs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l_Lean_Syntax_getArgs(x_1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__1___rarg(x_2, x_4, x_9, x_10, x_3);
lean_dec(x_4);
return x_11;
}
}
}
}
lean_object* l_Lean_Syntax_foldArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_foldArgs___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__1___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Syntax_foldArgs___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_foldArgs___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = x_1 + x_7;
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_4 == x_5;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_box_usize(x_4);
x_12 = lean_box_usize(x_5);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_6);
return x_17;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_forArgsM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l_Lean_Syntax_getArgs(x_2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_5, x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_19 = lean_box(0);
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg(x_1, x_3, x_4, x_17, x_18, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Syntax_forArgsM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_forArgsM___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
lean_object* l_Lean_Syntax_forArgsM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_forArgsM___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Trie(lean_object*);
lean_object* initialize_Lean_Data_Position(lean_object*);
lean_object* initialize_Lean_Syntax(lean_object*);
lean_object* initialize_Lean_ToExpr(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_Attributes(lean_object*);
lean_object* initialize_Lean_Message(lean_object*);
lean_object* initialize_Lean_Compiler_InitAttr(lean_object*);
lean_object* initialize_Lean_ResolveName(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Parser_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Trie(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Position(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Syntax(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ToExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Attributes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InitAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ResolveName(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_maxPrec = _init_l_Lean_Parser_maxPrec();
lean_mark_persistent(l_Lean_Parser_maxPrec);
l_Lean_Parser_leadPrec = _init_l_Lean_Parser_leadPrec();
lean_mark_persistent(l_Lean_Parser_leadPrec);
l_Lean_Parser_TokenCacheEntry_startPos___default = _init_l_Lean_Parser_TokenCacheEntry_startPos___default();
lean_mark_persistent(l_Lean_Parser_TokenCacheEntry_startPos___default);
l_Lean_Parser_TokenCacheEntry_stopPos___default = _init_l_Lean_Parser_TokenCacheEntry_stopPos___default();
lean_mark_persistent(l_Lean_Parser_TokenCacheEntry_stopPos___default);
l_Lean_Parser_TokenCacheEntry_token___default = _init_l_Lean_Parser_TokenCacheEntry_token___default();
lean_mark_persistent(l_Lean_Parser_TokenCacheEntry_token___default);
l_Lean_Parser_instInhabitedInputContext___closed__1 = _init_l_Lean_Parser_instInhabitedInputContext___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext___closed__1);
l_Lean_Parser_instInhabitedInputContext = _init_l_Lean_Parser_instInhabitedInputContext();
lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext);
l_Lean_Parser_ParserModuleContext_currNamespace___default = _init_l_Lean_Parser_ParserModuleContext_currNamespace___default();
lean_mark_persistent(l_Lean_Parser_ParserModuleContext_currNamespace___default);
l_Lean_Parser_ParserModuleContext_openDecls___default = _init_l_Lean_Parser_ParserModuleContext_openDecls___default();
lean_mark_persistent(l_Lean_Parser_ParserModuleContext_openDecls___default);
l_Lean_Parser_ParserContext_insideQuot___default = _init_l_Lean_Parser_ParserContext_insideQuot___default();
l_Lean_Parser_ParserContext_suppressInsideQuot___default = _init_l_Lean_Parser_ParserContext_suppressInsideQuot___default();
l_Lean_Parser_ParserContext_savedPos_x3f___default = _init_l_Lean_Parser_ParserContext_savedPos_x3f___default();
lean_mark_persistent(l_Lean_Parser_ParserContext_savedPos_x3f___default);
l_Lean_Parser_ParserContext_forbiddenTk_x3f___default = _init_l_Lean_Parser_ParserContext_forbiddenTk_x3f___default();
lean_mark_persistent(l_Lean_Parser_ParserContext_forbiddenTk_x3f___default);
l_Lean_Parser_Error_unexpected___default = _init_l_Lean_Parser_Error_unexpected___default();
lean_mark_persistent(l_Lean_Parser_Error_unexpected___default);
l_Lean_Parser_Error_expected___default = _init_l_Lean_Parser_Error_expected___default();
lean_mark_persistent(l_Lean_Parser_Error_expected___default);
l_Lean_Parser_instInhabitedError___closed__1 = _init_l_Lean_Parser_instInhabitedError___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedError___closed__1);
l_Lean_Parser_instInhabitedError = _init_l_Lean_Parser_instInhabitedError();
lean_mark_persistent(l_Lean_Parser_instInhabitedError);
l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString___closed__1 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString___closed__1);
l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___closed__1 = _init_l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___closed__1);
l_Lean_Parser_Error_toString___closed__1 = _init_l_Lean_Parser_Error_toString___closed__1();
lean_mark_persistent(l_Lean_Parser_Error_toString___closed__1);
l_Lean_Parser_Error_toString___closed__2 = _init_l_Lean_Parser_Error_toString___closed__2();
lean_mark_persistent(l_Lean_Parser_Error_toString___closed__2);
l_Lean_Parser_Error_toString___closed__3 = _init_l_Lean_Parser_Error_toString___closed__3();
lean_mark_persistent(l_Lean_Parser_Error_toString___closed__3);
l_Lean_Parser_Error_toString___closed__4 = _init_l_Lean_Parser_Error_toString___closed__4();
lean_mark_persistent(l_Lean_Parser_Error_toString___closed__4);
l_Lean_Parser_Error_instToStringError___closed__1 = _init_l_Lean_Parser_Error_instToStringError___closed__1();
lean_mark_persistent(l_Lean_Parser_Error_instToStringError___closed__1);
l_Lean_Parser_Error_instToStringError = _init_l_Lean_Parser_Error_instToStringError();
lean_mark_persistent(l_Lean_Parser_Error_instToStringError);
l_Lean_Parser_Error_instBEqError___closed__1 = _init_l_Lean_Parser_Error_instBEqError___closed__1();
lean_mark_persistent(l_Lean_Parser_Error_instBEqError___closed__1);
l_Lean_Parser_Error_instBEqError = _init_l_Lean_Parser_Error_instBEqError();
lean_mark_persistent(l_Lean_Parser_Error_instBEqError);
l_Lean_Parser_ParserState_stxStack___default = _init_l_Lean_Parser_ParserState_stxStack___default();
lean_mark_persistent(l_Lean_Parser_ParserState_stxStack___default);
l_Lean_Parser_ParserState_pos___default = _init_l_Lean_Parser_ParserState_pos___default();
lean_mark_persistent(l_Lean_Parser_ParserState_pos___default);
l_Lean_Parser_ParserState_errorMsg___default = _init_l_Lean_Parser_ParserState_errorMsg___default();
lean_mark_persistent(l_Lean_Parser_ParserState_errorMsg___default);
l_Lean_Parser_ParserState_mkEOIError___closed__1 = _init_l_Lean_Parser_ParserState_mkEOIError___closed__1();
lean_mark_persistent(l_Lean_Parser_ParserState_mkEOIError___closed__1);
l_Lean_Parser_instInhabitedFirstTokens = _init_l_Lean_Parser_instInhabitedFirstTokens();
lean_mark_persistent(l_Lean_Parser_instInhabitedFirstTokens);
l_Lean_Parser_FirstTokens_toStr___closed__1 = _init_l_Lean_Parser_FirstTokens_toStr___closed__1();
lean_mark_persistent(l_Lean_Parser_FirstTokens_toStr___closed__1);
l_Lean_Parser_FirstTokens_toStr___closed__2 = _init_l_Lean_Parser_FirstTokens_toStr___closed__2();
lean_mark_persistent(l_Lean_Parser_FirstTokens_toStr___closed__2);
l_Lean_Parser_FirstTokens_instToStringFirstTokens___closed__1 = _init_l_Lean_Parser_FirstTokens_instToStringFirstTokens___closed__1();
lean_mark_persistent(l_Lean_Parser_FirstTokens_instToStringFirstTokens___closed__1);
l_Lean_Parser_FirstTokens_instToStringFirstTokens = _init_l_Lean_Parser_FirstTokens_instToStringFirstTokens();
lean_mark_persistent(l_Lean_Parser_FirstTokens_instToStringFirstTokens);
l_Lean_Parser_ParserInfo_firstTokens___default = _init_l_Lean_Parser_ParserInfo_firstTokens___default();
lean_mark_persistent(l_Lean_Parser_ParserInfo_firstTokens___default);
l_Lean_Parser_instInhabitedParserInfo___closed__1 = _init_l_Lean_Parser_instInhabitedParserInfo___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserInfo___closed__1);
l_Lean_Parser_instInhabitedParserInfo___closed__2 = _init_l_Lean_Parser_instInhabitedParserInfo___closed__2();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserInfo___closed__2);
l_Lean_Parser_instInhabitedParserInfo___closed__3 = _init_l_Lean_Parser_instInhabitedParserInfo___closed__3();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserInfo___closed__3);
l_Lean_Parser_instInhabitedParserInfo = _init_l_Lean_Parser_instInhabitedParserInfo();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserInfo);
l_Lean_Parser_Parser_info___default___closed__1 = _init_l_Lean_Parser_Parser_info___default___closed__1();
lean_mark_persistent(l_Lean_Parser_Parser_info___default___closed__1);
l_Lean_Parser_Parser_info___default___closed__2 = _init_l_Lean_Parser_Parser_info___default___closed__2();
lean_mark_persistent(l_Lean_Parser_Parser_info___default___closed__2);
l_Lean_Parser_Parser_info___default___closed__3 = _init_l_Lean_Parser_Parser_info___default___closed__3();
lean_mark_persistent(l_Lean_Parser_Parser_info___default___closed__3);
l_Lean_Parser_Parser_info___default = _init_l_Lean_Parser_Parser_info___default();
lean_mark_persistent(l_Lean_Parser_Parser_info___default);
l_Lean_Parser_instInhabitedParser___closed__1 = _init_l_Lean_Parser_instInhabitedParser___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedParser___closed__1);
l_Lean_Parser_instInhabitedParser___closed__2 = _init_l_Lean_Parser_instInhabitedParser___closed__2();
lean_mark_persistent(l_Lean_Parser_instInhabitedParser___closed__2);
l_Lean_Parser_instInhabitedParser = _init_l_Lean_Parser_instInhabitedParser();
lean_mark_persistent(l_Lean_Parser_instInhabitedParser);
l_Lean_Parser_epsilonInfo___closed__1 = _init_l_Lean_Parser_epsilonInfo___closed__1();
lean_mark_persistent(l_Lean_Parser_epsilonInfo___closed__1);
l_Lean_Parser_epsilonInfo___closed__2 = _init_l_Lean_Parser_epsilonInfo___closed__2();
lean_mark_persistent(l_Lean_Parser_epsilonInfo___closed__2);
l_Lean_Parser_epsilonInfo___closed__3 = _init_l_Lean_Parser_epsilonInfo___closed__3();
lean_mark_persistent(l_Lean_Parser_epsilonInfo___closed__3);
l_Lean_Parser_epsilonInfo = _init_l_Lean_Parser_epsilonInfo();
lean_mark_persistent(l_Lean_Parser_epsilonInfo);
l_Lean_Parser_instAndThenParser___closed__1 = _init_l_Lean_Parser_instAndThenParser___closed__1();
lean_mark_persistent(l_Lean_Parser_instAndThenParser___closed__1);
l_Lean_Parser_instAndThenParser = _init_l_Lean_Parser_instAndThenParser();
lean_mark_persistent(l_Lean_Parser_instAndThenParser);
l_Lean_Parser_errorAtSavedPos___closed__1 = _init_l_Lean_Parser_errorAtSavedPos___closed__1();
lean_mark_persistent(l_Lean_Parser_errorAtSavedPos___closed__1);
l_Lean_Parser_checkPrecFn___closed__1 = _init_l_Lean_Parser_checkPrecFn___closed__1();
lean_mark_persistent(l_Lean_Parser_checkPrecFn___closed__1);
l_Lean_Parser_checkInsideQuotFn___closed__1 = _init_l_Lean_Parser_checkInsideQuotFn___closed__1();
lean_mark_persistent(l_Lean_Parser_checkInsideQuotFn___closed__1);
l_Lean_Parser_checkInsideQuot___closed__1 = _init_l_Lean_Parser_checkInsideQuot___closed__1();
lean_mark_persistent(l_Lean_Parser_checkInsideQuot___closed__1);
l_Lean_Parser_checkInsideQuot___closed__2 = _init_l_Lean_Parser_checkInsideQuot___closed__2();
lean_mark_persistent(l_Lean_Parser_checkInsideQuot___closed__2);
l_Lean_Parser_checkInsideQuot = _init_l_Lean_Parser_checkInsideQuot();
lean_mark_persistent(l_Lean_Parser_checkInsideQuot);
l_Lean_Parser_checkOutsideQuotFn___closed__1 = _init_l_Lean_Parser_checkOutsideQuotFn___closed__1();
lean_mark_persistent(l_Lean_Parser_checkOutsideQuotFn___closed__1);
l_Lean_Parser_checkOutsideQuot___closed__1 = _init_l_Lean_Parser_checkOutsideQuot___closed__1();
lean_mark_persistent(l_Lean_Parser_checkOutsideQuot___closed__1);
l_Lean_Parser_checkOutsideQuot___closed__2 = _init_l_Lean_Parser_checkOutsideQuot___closed__2();
lean_mark_persistent(l_Lean_Parser_checkOutsideQuot___closed__2);
l_Lean_Parser_checkOutsideQuot = _init_l_Lean_Parser_checkOutsideQuot();
lean_mark_persistent(l_Lean_Parser_checkOutsideQuot);
l_Lean_Parser_instOrElseParser___closed__1 = _init_l_Lean_Parser_instOrElseParser___closed__1();
lean_mark_persistent(l_Lean_Parser_instOrElseParser___closed__1);
l_Lean_Parser_instOrElseParser = _init_l_Lean_Parser_instOrElseParser();
lean_mark_persistent(l_Lean_Parser_instOrElseParser);
l_Lean_Parser_notFollowedByFn___closed__1 = _init_l_Lean_Parser_notFollowedByFn___closed__1();
lean_mark_persistent(l_Lean_Parser_notFollowedByFn___closed__1);
l_Lean_Parser_manyAux___closed__1 = _init_l_Lean_Parser_manyAux___closed__1();
lean_mark_persistent(l_Lean_Parser_manyAux___closed__1);
l_Lean_Parser_many1Unbox___closed__1 = _init_l_Lean_Parser_many1Unbox___closed__1();
lean_mark_persistent(l_Lean_Parser_many1Unbox___closed__1);
l_Lean_Parser_whitespace___closed__1 = _init_l_Lean_Parser_whitespace___closed__1();
lean_mark_persistent(l_Lean_Parser_whitespace___closed__1);
l_Lean_Parser_hexDigitFn___closed__1 = _init_l_Lean_Parser_hexDigitFn___closed__1();
lean_mark_persistent(l_Lean_Parser_hexDigitFn___closed__1);
l_Lean_Parser_quotedCharCoreFn___closed__1 = _init_l_Lean_Parser_quotedCharCoreFn___closed__1();
lean_mark_persistent(l_Lean_Parser_quotedCharCoreFn___closed__1);
l_Lean_Parser_quotedCharFn___closed__1 = _init_l_Lean_Parser_quotedCharFn___closed__1();
lean_mark_persistent(l_Lean_Parser_quotedCharFn___closed__1);
l_Lean_Parser_charLitFnAux___closed__1 = _init_l_Lean_Parser_charLitFnAux___closed__1();
lean_mark_persistent(l_Lean_Parser_charLitFnAux___closed__1);
l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1 = _init_l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1();
lean_mark_persistent(l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1);
l_Lean_Parser_binNumberFn___closed__1 = _init_l_Lean_Parser_binNumberFn___closed__1();
lean_mark_persistent(l_Lean_Parser_binNumberFn___closed__1);
l_Lean_Parser_binNumberFn___closed__2 = _init_l_Lean_Parser_binNumberFn___closed__2();
lean_mark_persistent(l_Lean_Parser_binNumberFn___closed__2);
l_Lean_Parser_octalNumberFn___closed__1 = _init_l_Lean_Parser_octalNumberFn___closed__1();
lean_mark_persistent(l_Lean_Parser_octalNumberFn___closed__1);
l_Lean_Parser_octalNumberFn___closed__2 = _init_l_Lean_Parser_octalNumberFn___closed__2();
lean_mark_persistent(l_Lean_Parser_octalNumberFn___closed__2);
l_Lean_Parser_hexNumberFn___closed__1 = _init_l_Lean_Parser_hexNumberFn___closed__1();
lean_mark_persistent(l_Lean_Parser_hexNumberFn___closed__1);
l_Lean_Parser_hexNumberFn___closed__2 = _init_l_Lean_Parser_hexNumberFn___closed__2();
lean_mark_persistent(l_Lean_Parser_hexNumberFn___closed__2);
l_Lean_Parser_numberFnAux___closed__1 = _init_l_Lean_Parser_numberFnAux___closed__1();
lean_mark_persistent(l_Lean_Parser_numberFnAux___closed__1);
l_Lean_Parser_mkTokenAndFixPos___closed__1 = _init_l_Lean_Parser_mkTokenAndFixPos___closed__1();
lean_mark_persistent(l_Lean_Parser_mkTokenAndFixPos___closed__1);
l_Lean_Parser_mkTokenAndFixPos___closed__2 = _init_l_Lean_Parser_mkTokenAndFixPos___closed__2();
lean_mark_persistent(l_Lean_Parser_mkTokenAndFixPos___closed__2);
l_Lean_Parser_identFnAux_parse___closed__1 = _init_l_Lean_Parser_identFnAux_parse___closed__1();
lean_mark_persistent(l_Lean_Parser_identFnAux_parse___closed__1);
l_Lean_Parser_identFnAux_parse___closed__2 = _init_l_Lean_Parser_identFnAux_parse___closed__2();
lean_mark_persistent(l_Lean_Parser_identFnAux_parse___closed__2);
l_Lean_Parser_identFnAux_parse___closed__3 = _init_l_Lean_Parser_identFnAux_parse___closed__3();
lean_mark_persistent(l_Lean_Parser_identFnAux_parse___closed__3);
l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__1 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__1);
l_Lean_Parser_symbolInfo___closed__1 = _init_l_Lean_Parser_symbolInfo___closed__1();
lean_mark_persistent(l_Lean_Parser_symbolInfo___closed__1);
l_Lean_Parser_nonReservedSymbolInfo___closed__1 = _init_l_Lean_Parser_nonReservedSymbolInfo___closed__1();
lean_mark_persistent(l_Lean_Parser_nonReservedSymbolInfo___closed__1);
l_Lean_Parser_nonReservedSymbolInfo___closed__2 = _init_l_Lean_Parser_nonReservedSymbolInfo___closed__2();
lean_mark_persistent(l_Lean_Parser_nonReservedSymbolInfo___closed__2);
l_Lean_Parser_nonReservedSymbolInfo___closed__3 = _init_l_Lean_Parser_nonReservedSymbolInfo___closed__3();
lean_mark_persistent(l_Lean_Parser_nonReservedSymbolInfo___closed__3);
l_Lean_Parser_unicodeSymbolInfo___closed__1 = _init_l_Lean_Parser_unicodeSymbolInfo___closed__1();
lean_mark_persistent(l_Lean_Parser_unicodeSymbolInfo___closed__1);
l_Lean_Parser_unicodeSymbolFn___closed__1 = _init_l_Lean_Parser_unicodeSymbolFn___closed__1();
lean_mark_persistent(l_Lean_Parser_unicodeSymbolFn___closed__1);
l_Lean_Parser_mkAtomicInfo___closed__1 = _init_l_Lean_Parser_mkAtomicInfo___closed__1();
lean_mark_persistent(l_Lean_Parser_mkAtomicInfo___closed__1);
l_Lean_Parser_mkAtomicInfo___closed__2 = _init_l_Lean_Parser_mkAtomicInfo___closed__2();
lean_mark_persistent(l_Lean_Parser_mkAtomicInfo___closed__2);
l_Lean_Parser_numLitNoAntiquot___closed__1 = _init_l_Lean_Parser_numLitNoAntiquot___closed__1();
lean_mark_persistent(l_Lean_Parser_numLitNoAntiquot___closed__1);
l_Lean_Parser_numLitNoAntiquot___closed__2 = _init_l_Lean_Parser_numLitNoAntiquot___closed__2();
lean_mark_persistent(l_Lean_Parser_numLitNoAntiquot___closed__2);
l_Lean_Parser_numLitNoAntiquot___closed__3 = _init_l_Lean_Parser_numLitNoAntiquot___closed__3();
lean_mark_persistent(l_Lean_Parser_numLitNoAntiquot___closed__3);
l_Lean_Parser_numLitNoAntiquot = _init_l_Lean_Parser_numLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_numLitNoAntiquot);
l_Lean_Parser_scientificLitFn___closed__1 = _init_l_Lean_Parser_scientificLitFn___closed__1();
lean_mark_persistent(l_Lean_Parser_scientificLitFn___closed__1);
l_Lean_Parser_scientificLitNoAntiquot___closed__1 = _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1();
lean_mark_persistent(l_Lean_Parser_scientificLitNoAntiquot___closed__1);
l_Lean_Parser_scientificLitNoAntiquot___closed__2 = _init_l_Lean_Parser_scientificLitNoAntiquot___closed__2();
lean_mark_persistent(l_Lean_Parser_scientificLitNoAntiquot___closed__2);
l_Lean_Parser_scientificLitNoAntiquot___closed__3 = _init_l_Lean_Parser_scientificLitNoAntiquot___closed__3();
lean_mark_persistent(l_Lean_Parser_scientificLitNoAntiquot___closed__3);
l_Lean_Parser_scientificLitNoAntiquot = _init_l_Lean_Parser_scientificLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_scientificLitNoAntiquot);
l_Lean_Parser_strLitFn___closed__1 = _init_l_Lean_Parser_strLitFn___closed__1();
lean_mark_persistent(l_Lean_Parser_strLitFn___closed__1);
l_Lean_Parser_strLitNoAntiquot___closed__1 = _init_l_Lean_Parser_strLitNoAntiquot___closed__1();
lean_mark_persistent(l_Lean_Parser_strLitNoAntiquot___closed__1);
l_Lean_Parser_strLitNoAntiquot___closed__2 = _init_l_Lean_Parser_strLitNoAntiquot___closed__2();
lean_mark_persistent(l_Lean_Parser_strLitNoAntiquot___closed__2);
l_Lean_Parser_strLitNoAntiquot___closed__3 = _init_l_Lean_Parser_strLitNoAntiquot___closed__3();
lean_mark_persistent(l_Lean_Parser_strLitNoAntiquot___closed__3);
l_Lean_Parser_strLitNoAntiquot = _init_l_Lean_Parser_strLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_strLitNoAntiquot);
l_Lean_Parser_charLitFn___closed__1 = _init_l_Lean_Parser_charLitFn___closed__1();
lean_mark_persistent(l_Lean_Parser_charLitFn___closed__1);
l_Lean_Parser_charLitNoAntiquot___closed__1 = _init_l_Lean_Parser_charLitNoAntiquot___closed__1();
lean_mark_persistent(l_Lean_Parser_charLitNoAntiquot___closed__1);
l_Lean_Parser_charLitNoAntiquot___closed__2 = _init_l_Lean_Parser_charLitNoAntiquot___closed__2();
lean_mark_persistent(l_Lean_Parser_charLitNoAntiquot___closed__2);
l_Lean_Parser_charLitNoAntiquot___closed__3 = _init_l_Lean_Parser_charLitNoAntiquot___closed__3();
lean_mark_persistent(l_Lean_Parser_charLitNoAntiquot___closed__3);
l_Lean_Parser_charLitNoAntiquot = _init_l_Lean_Parser_charLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_charLitNoAntiquot);
l_Lean_Parser_nameLitFn___closed__1 = _init_l_Lean_Parser_nameLitFn___closed__1();
lean_mark_persistent(l_Lean_Parser_nameLitFn___closed__1);
l_Lean_Parser_nameLitNoAntiquot___closed__1 = _init_l_Lean_Parser_nameLitNoAntiquot___closed__1();
lean_mark_persistent(l_Lean_Parser_nameLitNoAntiquot___closed__1);
l_Lean_Parser_nameLitNoAntiquot___closed__2 = _init_l_Lean_Parser_nameLitNoAntiquot___closed__2();
lean_mark_persistent(l_Lean_Parser_nameLitNoAntiquot___closed__2);
l_Lean_Parser_nameLitNoAntiquot___closed__3 = _init_l_Lean_Parser_nameLitNoAntiquot___closed__3();
lean_mark_persistent(l_Lean_Parser_nameLitNoAntiquot___closed__3);
l_Lean_Parser_nameLitNoAntiquot = _init_l_Lean_Parser_nameLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_nameLitNoAntiquot);
l_Lean_Parser_identFn___closed__1 = _init_l_Lean_Parser_identFn___closed__1();
lean_mark_persistent(l_Lean_Parser_identFn___closed__1);
l_Lean_Parser_identNoAntiquot___closed__1 = _init_l_Lean_Parser_identNoAntiquot___closed__1();
lean_mark_persistent(l_Lean_Parser_identNoAntiquot___closed__1);
l_Lean_Parser_identNoAntiquot___closed__2 = _init_l_Lean_Parser_identNoAntiquot___closed__2();
lean_mark_persistent(l_Lean_Parser_identNoAntiquot___closed__2);
l_Lean_Parser_identNoAntiquot___closed__3 = _init_l_Lean_Parser_identNoAntiquot___closed__3();
lean_mark_persistent(l_Lean_Parser_identNoAntiquot___closed__3);
l_Lean_Parser_identNoAntiquot = _init_l_Lean_Parser_identNoAntiquot();
lean_mark_persistent(l_Lean_Parser_identNoAntiquot);
l_Lean_Parser_rawIdentNoAntiquot___closed__1 = _init_l_Lean_Parser_rawIdentNoAntiquot___closed__1();
lean_mark_persistent(l_Lean_Parser_rawIdentNoAntiquot___closed__1);
l_Lean_Parser_rawIdentNoAntiquot___closed__2 = _init_l_Lean_Parser_rawIdentNoAntiquot___closed__2();
lean_mark_persistent(l_Lean_Parser_rawIdentNoAntiquot___closed__2);
l_Lean_Parser_rawIdentNoAntiquot = _init_l_Lean_Parser_rawIdentNoAntiquot();
lean_mark_persistent(l_Lean_Parser_rawIdentNoAntiquot);
l_Lean_Parser_identEqFn___closed__1 = _init_l_Lean_Parser_identEqFn___closed__1();
lean_mark_persistent(l_Lean_Parser_identEqFn___closed__1);
l_Lean_Parser_invalidLongestMatchParser___closed__1 = _init_l_Lean_Parser_invalidLongestMatchParser___closed__1();
lean_mark_persistent(l_Lean_Parser_invalidLongestMatchParser___closed__1);
l_Lean_Parser_longestMatchFn___closed__1 = _init_l_Lean_Parser_longestMatchFn___closed__1();
lean_mark_persistent(l_Lean_Parser_longestMatchFn___closed__1);
l_Lean_Parser_anyOfFn___closed__1 = _init_l_Lean_Parser_anyOfFn___closed__1();
lean_mark_persistent(l_Lean_Parser_anyOfFn___closed__1);
l_Lean_Parser_eoiFn___closed__1 = _init_l_Lean_Parser_eoiFn___closed__1();
lean_mark_persistent(l_Lean_Parser_eoiFn___closed__1);
l_Lean_Parser_eoi___closed__1 = _init_l_Lean_Parser_eoi___closed__1();
lean_mark_persistent(l_Lean_Parser_eoi___closed__1);
l_Lean_Parser_eoi___closed__2 = _init_l_Lean_Parser_eoi___closed__2();
lean_mark_persistent(l_Lean_Parser_eoi___closed__2);
l_Lean_Parser_eoi = _init_l_Lean_Parser_eoi();
lean_mark_persistent(l_Lean_Parser_eoi);
l_Lean_Parser_PrattParsingTables_leadingTable___default = _init_l_Lean_Parser_PrattParsingTables_leadingTable___default();
lean_mark_persistent(l_Lean_Parser_PrattParsingTables_leadingTable___default);
l_Lean_Parser_PrattParsingTables_leadingParsers___default = _init_l_Lean_Parser_PrattParsingTables_leadingParsers___default();
lean_mark_persistent(l_Lean_Parser_PrattParsingTables_leadingParsers___default);
l_Lean_Parser_PrattParsingTables_trailingTable___default = _init_l_Lean_Parser_PrattParsingTables_trailingTable___default();
lean_mark_persistent(l_Lean_Parser_PrattParsingTables_trailingTable___default);
l_Lean_Parser_PrattParsingTables_trailingParsers___default = _init_l_Lean_Parser_PrattParsingTables_trailingParsers___default();
lean_mark_persistent(l_Lean_Parser_PrattParsingTables_trailingParsers___default);
l_Lean_Parser_instInhabitedPrattParsingTables___closed__1 = _init_l_Lean_Parser_instInhabitedPrattParsingTables___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedPrattParsingTables___closed__1);
l_Lean_Parser_instInhabitedPrattParsingTables = _init_l_Lean_Parser_instInhabitedPrattParsingTables();
lean_mark_persistent(l_Lean_Parser_instInhabitedPrattParsingTables);
l_Lean_Parser_instInhabitedLeadingIdentBehavior = _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior();
l_Lean_Parser_instBEqLeadingIdentBehavior___closed__1 = _init_l_Lean_Parser_instBEqLeadingIdentBehavior___closed__1();
lean_mark_persistent(l_Lean_Parser_instBEqLeadingIdentBehavior___closed__1);
l_Lean_Parser_instBEqLeadingIdentBehavior = _init_l_Lean_Parser_instBEqLeadingIdentBehavior();
lean_mark_persistent(l_Lean_Parser_instBEqLeadingIdentBehavior);
l_Lean_Parser_instInhabitedParserCategory___closed__1 = _init_l_Lean_Parser_instInhabitedParserCategory___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserCategory___closed__1);
l_Lean_Parser_instInhabitedParserCategory = _init_l_Lean_Parser_instInhabitedParserCategory();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserCategory);
l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6172____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6172____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6172____closed__1);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6172_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_categoryParserFnRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_categoryParserFnRef);
lean_dec_ref(res);
l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6190____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6190____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6190____closed__1);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_6190_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_categoryParserFnExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_categoryParserFnExtension);
lean_dec_ref(res);
l_Lean_Parser_checkNoImmediateColon___elambda__1___closed__1 = _init_l_Lean_Parser_checkNoImmediateColon___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_checkNoImmediateColon___elambda__1___closed__1);
l_Lean_Parser_checkNoImmediateColon___closed__1 = _init_l_Lean_Parser_checkNoImmediateColon___closed__1();
lean_mark_persistent(l_Lean_Parser_checkNoImmediateColon___closed__1);
l_Lean_Parser_checkNoImmediateColon___closed__2 = _init_l_Lean_Parser_checkNoImmediateColon___closed__2();
lean_mark_persistent(l_Lean_Parser_checkNoImmediateColon___closed__2);
l_Lean_Parser_checkNoImmediateColon = _init_l_Lean_Parser_checkNoImmediateColon();
lean_mark_persistent(l_Lean_Parser_checkNoImmediateColon);
l_Lean_Parser_pushNone___closed__1 = _init_l_Lean_Parser_pushNone___closed__1();
lean_mark_persistent(l_Lean_Parser_pushNone___closed__1);
l_Lean_Parser_pushNone___closed__2 = _init_l_Lean_Parser_pushNone___closed__2();
lean_mark_persistent(l_Lean_Parser_pushNone___closed__2);
l_Lean_Parser_pushNone = _init_l_Lean_Parser_pushNone();
lean_mark_persistent(l_Lean_Parser_pushNone);
l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__1 = _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__1);
l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__2 = _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__2);
l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__3 = _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__3);
l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__4 = _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__4();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__4);
l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__5 = _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__5();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__5);
l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__6 = _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__6();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__6);
l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__7 = _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__7();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__7);
l_Lean_Parser_antiquotNestedExpr___closed__1 = _init_l_Lean_Parser_antiquotNestedExpr___closed__1();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___closed__1);
l_Lean_Parser_antiquotNestedExpr___closed__2 = _init_l_Lean_Parser_antiquotNestedExpr___closed__2();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___closed__2);
l_Lean_Parser_antiquotNestedExpr___closed__3 = _init_l_Lean_Parser_antiquotNestedExpr___closed__3();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___closed__3);
l_Lean_Parser_antiquotNestedExpr___closed__4 = _init_l_Lean_Parser_antiquotNestedExpr___closed__4();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___closed__4);
l_Lean_Parser_antiquotNestedExpr___closed__5 = _init_l_Lean_Parser_antiquotNestedExpr___closed__5();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___closed__5);
l_Lean_Parser_antiquotNestedExpr___closed__6 = _init_l_Lean_Parser_antiquotNestedExpr___closed__6();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___closed__6);
l_Lean_Parser_antiquotNestedExpr___closed__7 = _init_l_Lean_Parser_antiquotNestedExpr___closed__7();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___closed__7);
l_Lean_Parser_antiquotNestedExpr___closed__8 = _init_l_Lean_Parser_antiquotNestedExpr___closed__8();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___closed__8);
l_Lean_Parser_antiquotNestedExpr = _init_l_Lean_Parser_antiquotNestedExpr();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr);
l_Lean_Parser_antiquotExpr___closed__1 = _init_l_Lean_Parser_antiquotExpr___closed__1();
lean_mark_persistent(l_Lean_Parser_antiquotExpr___closed__1);
l_Lean_Parser_antiquotExpr___closed__2 = _init_l_Lean_Parser_antiquotExpr___closed__2();
lean_mark_persistent(l_Lean_Parser_antiquotExpr___closed__2);
l_Lean_Parser_antiquotExpr___closed__3 = _init_l_Lean_Parser_antiquotExpr___closed__3();
lean_mark_persistent(l_Lean_Parser_antiquotExpr___closed__3);
l_Lean_Parser_antiquotExpr = _init_l_Lean_Parser_antiquotExpr();
lean_mark_persistent(l_Lean_Parser_antiquotExpr);
l_Lean_Parser_mkAntiquot___closed__1 = _init_l_Lean_Parser_mkAntiquot___closed__1();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__1);
l_Lean_Parser_mkAntiquot___closed__2 = _init_l_Lean_Parser_mkAntiquot___closed__2();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__2);
l_Lean_Parser_mkAntiquot___closed__3 = _init_l_Lean_Parser_mkAntiquot___closed__3();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__3);
l_Lean_Parser_mkAntiquot___closed__4 = _init_l_Lean_Parser_mkAntiquot___closed__4();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__4);
l_Lean_Parser_mkAntiquot___closed__5 = _init_l_Lean_Parser_mkAntiquot___closed__5();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__5);
l_Lean_Parser_mkAntiquot___closed__6 = _init_l_Lean_Parser_mkAntiquot___closed__6();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__6);
l_Lean_Parser_mkAntiquot___closed__7 = _init_l_Lean_Parser_mkAntiquot___closed__7();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__7);
l_Lean_Parser_mkAntiquot___closed__8 = _init_l_Lean_Parser_mkAntiquot___closed__8();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__8);
l_Lean_Parser_mkAntiquot___closed__9 = _init_l_Lean_Parser_mkAntiquot___closed__9();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__9);
l_Lean_Parser_mkAntiquot___closed__10 = _init_l_Lean_Parser_mkAntiquot___closed__10();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__10);
l_Lean_Parser_mkAntiquot___closed__11 = _init_l_Lean_Parser_mkAntiquot___closed__11();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__11);
l_Lean_Parser_mkAntiquot___closed__12 = _init_l_Lean_Parser_mkAntiquot___closed__12();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__12);
l_Lean_Parser_mkAntiquot___closed__13 = _init_l_Lean_Parser_mkAntiquot___closed__13();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__13);
l_Lean_Parser_mkAntiquot___closed__14 = _init_l_Lean_Parser_mkAntiquot___closed__14();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__14);
l_Lean_Parser_mkAntiquot___closed__15 = _init_l_Lean_Parser_mkAntiquot___closed__15();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__15);
l_Lean_Parser_mkAntiquot___closed__16 = _init_l_Lean_Parser_mkAntiquot___closed__16();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__16);
l_Lean_Parser_mkAntiquot___closed__17 = _init_l_Lean_Parser_mkAntiquot___closed__17();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__17);
l_Lean_Parser_mkAntiquot___closed__18 = _init_l_Lean_Parser_mkAntiquot___closed__18();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__18);
l_Lean_Parser_mkAntiquotSplice___closed__1 = _init_l_Lean_Parser_mkAntiquotSplice___closed__1();
lean_mark_persistent(l_Lean_Parser_mkAntiquotSplice___closed__1);
l_Lean_Parser_mkAntiquotSplice___closed__2 = _init_l_Lean_Parser_mkAntiquotSplice___closed__2();
lean_mark_persistent(l_Lean_Parser_mkAntiquotSplice___closed__2);
l_Lean_Parser_mkAntiquotSplice___closed__3 = _init_l_Lean_Parser_mkAntiquotSplice___closed__3();
lean_mark_persistent(l_Lean_Parser_mkAntiquotSplice___closed__3);
l_Lean_Parser_mkAntiquotSplice___closed__4 = _init_l_Lean_Parser_mkAntiquotSplice___closed__4();
lean_mark_persistent(l_Lean_Parser_mkAntiquotSplice___closed__4);
l_Lean_Parser_mkAntiquotSplice___closed__5 = _init_l_Lean_Parser_mkAntiquotSplice___closed__5();
lean_mark_persistent(l_Lean_Parser_mkAntiquotSplice___closed__5);
l_Lean_Parser_mkAntiquotSplice___closed__6 = _init_l_Lean_Parser_mkAntiquotSplice___closed__6();
lean_mark_persistent(l_Lean_Parser_mkAntiquotSplice___closed__6);
l_Lean_Parser_mkAntiquotSplice___closed__7 = _init_l_Lean_Parser_mkAntiquotSplice___closed__7();
lean_mark_persistent(l_Lean_Parser_mkAntiquotSplice___closed__7);
l_Lean_Parser_sepByElemParser___closed__1 = _init_l_Lean_Parser_sepByElemParser___closed__1();
lean_mark_persistent(l_Lean_Parser_sepByElemParser___closed__1);
l_Lean_Parser_categoryParserOfStackFn___closed__1 = _init_l_Lean_Parser_categoryParserOfStackFn___closed__1();
lean_mark_persistent(l_Lean_Parser_categoryParserOfStackFn___closed__1);
l_Lean_Parser_categoryParserOfStackFn___closed__2 = _init_l_Lean_Parser_categoryParserOfStackFn___closed__2();
lean_mark_persistent(l_Lean_Parser_categoryParserOfStackFn___closed__2);
l_Lean_Parser_evalParserConstUnsafe___closed__1 = _init_l_Lean_Parser_evalParserConstUnsafe___closed__1();
lean_mark_persistent(l_Lean_Parser_evalParserConstUnsafe___closed__1);
l_Lean_Parser_evalParserConstUnsafe___closed__2 = _init_l_Lean_Parser_evalParserConstUnsafe___closed__2();
lean_mark_persistent(l_Lean_Parser_evalParserConstUnsafe___closed__2);
l_Lean_Parser_evalParserConstUnsafe___closed__3 = _init_l_Lean_Parser_evalParserConstUnsafe___closed__3();
lean_mark_persistent(l_Lean_Parser_evalParserConstUnsafe___closed__3);
l_Lean_Parser_evalParserConstUnsafe___closed__4 = _init_l_Lean_Parser_evalParserConstUnsafe___closed__4();
lean_mark_persistent(l_Lean_Parser_evalParserConstUnsafe___closed__4);
l_Lean_Parser_parserOfStackFnUnsafe___closed__1 = _init_l_Lean_Parser_parserOfStackFnUnsafe___closed__1();
lean_mark_persistent(l_Lean_Parser_parserOfStackFnUnsafe___closed__1);
l_Lean_Parser_parserOfStackFnUnsafe___closed__2 = _init_l_Lean_Parser_parserOfStackFnUnsafe___closed__2();
lean_mark_persistent(l_Lean_Parser_parserOfStackFnUnsafe___closed__2);
l_Lean_Parser_parserOfStackFnUnsafe___closed__3 = _init_l_Lean_Parser_parserOfStackFnUnsafe___closed__3();
lean_mark_persistent(l_Lean_Parser_parserOfStackFnUnsafe___closed__3);
l_Lean_Parser_parserOfStackFnUnsafe___closed__4 = _init_l_Lean_Parser_parserOfStackFnUnsafe___closed__4();
lean_mark_persistent(l_Lean_Parser_parserOfStackFnUnsafe___closed__4);
l_Lean_Parser_parserOfStackFnUnsafe___closed__5 = _init_l_Lean_Parser_parserOfStackFnUnsafe___closed__5();
lean_mark_persistent(l_Lean_Parser_parserOfStackFnUnsafe___closed__5);
l_Lean_Parser_fieldIdxFn___closed__1 = _init_l_Lean_Parser_fieldIdxFn___closed__1();
lean_mark_persistent(l_Lean_Parser_fieldIdxFn___closed__1);
l_Lean_Parser_fieldIdx___closed__1 = _init_l_Lean_Parser_fieldIdx___closed__1();
lean_mark_persistent(l_Lean_Parser_fieldIdx___closed__1);
l_Lean_Parser_fieldIdx___closed__2 = _init_l_Lean_Parser_fieldIdx___closed__2();
lean_mark_persistent(l_Lean_Parser_fieldIdx___closed__2);
l_Lean_Parser_fieldIdx___closed__3 = _init_l_Lean_Parser_fieldIdx___closed__3();
lean_mark_persistent(l_Lean_Parser_fieldIdx___closed__3);
l_Lean_Parser_fieldIdx___closed__4 = _init_l_Lean_Parser_fieldIdx___closed__4();
lean_mark_persistent(l_Lean_Parser_fieldIdx___closed__4);
l_Lean_Parser_fieldIdx___closed__5 = _init_l_Lean_Parser_fieldIdx___closed__5();
lean_mark_persistent(l_Lean_Parser_fieldIdx___closed__5);
l_Lean_Parser_fieldIdx___closed__6 = _init_l_Lean_Parser_fieldIdx___closed__6();
lean_mark_persistent(l_Lean_Parser_fieldIdx___closed__6);
l_Lean_Parser_fieldIdx___closed__7 = _init_l_Lean_Parser_fieldIdx___closed__7();
lean_mark_persistent(l_Lean_Parser_fieldIdx___closed__7);
l_Lean_Parser_fieldIdx = _init_l_Lean_Parser_fieldIdx();
lean_mark_persistent(l_Lean_Parser_fieldIdx);
l_Lean_Parser_skip___closed__1 = _init_l_Lean_Parser_skip___closed__1();
lean_mark_persistent(l_Lean_Parser_skip___closed__1);
l_Lean_Parser_skip = _init_l_Lean_Parser_skip();
lean_mark_persistent(l_Lean_Parser_skip);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
