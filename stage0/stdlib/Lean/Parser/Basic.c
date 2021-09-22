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
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol___boxed(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserOfStack___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Parser_info___default___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedError;
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_fieldIdxKind;
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserInfo_firstTokens___default;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__1;
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailWs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__19;
static lean_object* l_Lean_Parser_finishCommentBlock_eoi___closed__1;
static lean_object* l_Lean_Parser_identFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__1___boxed(lean_object*);
static lean_object* l_Lean_Parser_dbgTraceStateFn___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedString;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_mkTokenAndFixPos___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptDot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___closed__1;
static lean_object* l_Lean_Parser_strLitNoAntiquot___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Parser_info___default;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_eoi___closed__2;
static lean_object* l_Lean_Parser_eoi___closed__1;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7595____closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyNoAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_notFollowedByFn___closed__1;
extern lean_object* l_Lean_nullKind;
static lean_object* l_Lean_Parser_Parser_info___default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_leadPrec;
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strLitNoAntiquot;
static lean_object* l_Lean_Parser_octalNumberFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailLinebreak(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Parser_eoi;
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn(lean_object*, lean_object*, lean_object*);
extern uint32_t l_Lean_idBeginEscape;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_errorMsg___default;
LEAN_EXPORT lean_object* l_Lean_Parser_optionaInfo___elambda__2(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_binNumberFn___closed__1;
static lean_object* l_Lean_Parser_hexNumberFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_checkInsideQuotFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux(lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_identEqFn___closed__1;
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux_parse___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__6;
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2(lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___at_Lean_Syntax_forArgsM___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_fieldIdx___closed__6;
static lean_object* l_Lean_Parser_errorAtSavedPos___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nameLitNoAntiquot;
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserInfo_collectKinds___default___boxed(lean_object*);
static lean_object* l_Lean_Parser_nameLitNoAntiquot___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_Parser_instInhabitedError___closed__1;
lean_object* l_Lean_Parser_Trie_matchPrefix___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___at_Lean_Syntax_forArgsM___spec__2___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Parser_octalNumberFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_minPrec;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected___elambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnRef;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Error_expected___default;
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone;
static lean_object* l_Lean_Parser_dbgTraceStateFn___closed__1;
static lean_object* l_Lean_Parser_checkNoImmediateColon___closed__1;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Parser_info___default___elambda__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_ParserContext_suppressInsideQuot___default;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserInfo_collectKinds___default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_PrattParsingTables_leadingTable___default;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__17;
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquotFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__3;
static lean_object* l_Lean_Parser_nonReservedSymbolInfo___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7595____lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strAux_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isLitKind(lean_object*);
lean_object* l_instInhabitedDepArrow___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instBEqError___closed__1;
static lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__1;
lean_object* lean_dbg_trace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_categoryParserOfStackFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe(lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__5;
extern lean_object* l_Lean_instHashableName;
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFn(lean_object*, lean_object*, lean_object*);
uint8_t l_Char_isDigit(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeStringParser___boxed(lean_object*);
static lean_object* l_Lean_Parser_evalParserConstUnsafe___closed__4;
LEAN_EXPORT lean_object* l_Array_qpartition_loop___at_Lean_Parser_Error_toString___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_binNumberFn___lambda__1(uint32_t);
static lean_object* l_Lean_Parser_evalParserConstUnsafe___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParserInfo___closed__1;
static lean_object* l_Lean_Parser_categoryParserFnExtension___closed__2;
static lean_object* l_Lean_Parser_nameLitNoAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_hexNumberFn___lambda__1(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkTokenAndFixPos___closed__2;
static lean_object* l_Lean_Parser_mkAntiquot___closed__9;
LEAN_EXPORT uint8_t l_Lean_Parser_octalNumberFn___lambda__1(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isIdRest___boxed(lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___elambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4(lean_object*);
static lean_object* l_Lean_Parser_instInhabitedInputContext___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserInfo_collectTokens___default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4(lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__4;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___elambda__1(uint32_t, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Parser_info___default___closed__1;
uint8_t l_Char_isWhitespace(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_atomicFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition(lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__11;
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFnAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrecFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_nameLitNoAntiquot___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Error_unexpected___default;
LEAN_EXPORT lean_object* l_Lean_Parser_tryAnti___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_checkPrecFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_TokenCacheEntry_startPos___default;
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTopFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_binNumberFn___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGeFn___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParserInfo___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_nameLitFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected___elambda__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__2___boxed(lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7614____closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nameLitKind;
static lean_object* l_Lean_Parser_categoryParserFnExtension___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1;
static lean_object* l_Lean_Parser_strLitFnAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuotFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParser___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_evalParserConstUnsafe___closed__8;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__9;
static lean_object* l_Lean_Parser_fieldIdx___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo;
static lean_object* l_Lean_Parser_dbgTraceStateFn___closed__2;
static lean_object* l_Lean_Parser_sepByElemParser___closed__3;
static lean_object* l_Lean_Parser_mkAntiquotSplice___closed__2;
static lean_object* l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrecFn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_takeWhileFn___lambda__1(lean_object*, uint32_t);
LEAN_EXPORT uint32_t l_Lean_Parser_getNext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toStringAux___at_Lean_Parser_FirstTokens_toStr___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo___elambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_many1Fn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_internal_parseQuotWithCurrentStage___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__13;
static lean_object* l_Lean_Parser_identFnAux_parse___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_identEqFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotExpr___closed__2;
static lean_object* l_Lean_Parser_scientificLitFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserCategory;
static lean_object* l_Lean_Parser_fieldIdx___closed__8;
static lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg___closed__1;
static lean_object* l_Lean_Parser_scientificLitFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_whitespace___closed__1;
static lean_object* l_Lean_Parser_scientificLitNoAntiquot___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_indexed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg;
static lean_object* l_Lean_Parser_mkAntiquotSplice___closed__9;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_invalidLongestMatchParser(lean_object*);
static lean_object* l_Lean_Parser_invalidLongestMatchParser___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape___boxed(lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__15;
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquotSplice___closed__4;
static lean_object* l_Lean_Parser_evalParserConstUnsafe___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__2(lean_object*);
static lean_object* l_Lean_Parser_checkOutsideQuot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConst___rarg___boxed(lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__4;
static lean_object* l_Lean_Parser_mkAntiquot___closed__18;
static lean_object* l_Lean_Parser_termParser___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_fieldIdx___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_longestMatchFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTopFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_setBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqError____x40_Lean_Parser_Basic___hyg_353____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_identNoAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr___elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkTokenAndFixPos___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_internal_parseQuotWithCurrentStage;
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharFn(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo___elambda__2(lean_object*);
static lean_object* l_Lean_Parser_strLitFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_Error_instToStringError;
static lean_object* l_Lean_Parser_strLitFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConst___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_FirstTokens_instToStringFirstTokens___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_errorAtSavedPos___closed__2;
static lean_object* l_Lean_Parser_dbgTraceStateFn___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_numLitNoAntiquot___closed__4;
static lean_object* l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257_(uint8_t, lean_object*);
static lean_object* l_Lean_Parser_sepByElemParser___closed__2;
static lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__6;
static lean_object* l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_lookaheadFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo___elambda__2(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_rawIdentNoAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFn___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__18;
extern lean_object* l_Lean_numLitKind;
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_Parser_numLitNoAntiquot___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeStringParser(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice___elambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__1;
static lean_object* l_Lean_Parser_fieldIdx___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore(lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__5;
uint8_t l_List_beq___at_Lean_Syntax_structEq___spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toStringAux___at_Lean_Parser_dbgTraceStateFn___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind;
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFnUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__14;
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs(lean_object*);
static lean_object* l_Lean_Parser_whitespace___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Error_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_skip___closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_numLitNoAntiquot___closed__2;
LEAN_EXPORT uint8_t l_Lean_Parser_whitespace___lambda__1(uint32_t);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_fieldIdx___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr;
static lean_object* l_Lean_Parser_instInhabitedParserCategory___closed__1;
uint8_t l_Substring_contains(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharDefault___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_toStringAux___at_Lean_Parser_dbgTraceStateFn___spec__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEqFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5(lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__16;
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_numLitFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_tryAnti(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior;
LEAN_EXPORT lean_object* l_Lean_Parser_optionaInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_seq(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_parserOfStackFnUnsafe___closed__4;
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_peekToken(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Error_toString___closed__4;
static lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxNodeKindSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_atomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_skip;
static lean_object* l_Lean_Parser_mkAntiquotSplice___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_charLitNoAntiquot___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_peekTokenAux(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_nonReservedSymbolInfo___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_dbgTraceStateFn___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_checkOutsideQuot___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailNoWs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux_parse___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailWs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_argPrec;
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoopStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7595____lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_sepByElemParser___closed__1;
static lean_object* l_Lean_Parser_charLitNoAntiquot___closed__2;
static lean_object* l_Lean_Parser_dbgTraceStateFn___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instAndThenParser(lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__3;
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn(lean_object*);
LEAN_EXPORT lean_object* l_List_eraseRepsAux___at_Lean_Parser_Error_toString___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFn(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__12;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7242____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_savedPos_x3f___default;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedInputContext;
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPosFn(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object*);
static lean_object* l_Lean_Parser_antiquotExpr___closed__1;
static lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__5;
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserOfStack(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__20;
uint8_t l_Lean_Option_get___at_Lean_ppExpr___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrec(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setCache(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__10;
static lean_object* l_Lean_Parser_incQuotDepth___closed__1;
lean_object* l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_48____spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_strLitNoAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_fieldIdx___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqLeadingIdentBehavior;
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getNext___boxed(lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquotFn___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_termParser___closed__2;
extern lean_object* l_Lean_choiceKind;
extern lean_object* l_Lean_charLitKind;
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_maxPrec;
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_strLitNoAntiquot___closed__4;
static lean_object* l_Lean_Parser_identFn___closed__2;
static lean_object* l_Lean_Parser_parserOfStackFnUnsafe___closed__3;
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6(lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_merge(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquotSplice___closed__1;
static lean_object* l_Lean_Parser_many1Unbox___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___elambda__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLitFn(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_PrattParsingTables_leadingParsers___default;
static lean_object* l_Lean_Parser_fieldIdx___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___elambda__2(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop(lean_object*, lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
static lean_object* l_Lean_Parser_instInhabitedPrattParsingTables___closed__1;
static lean_object* l_Lean_Parser_ParserState_mkEOIError___closed__1;
LEAN_EXPORT uint8_t l_Lean_Parser_isIdCont(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mergeOrElseErrors___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConst___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabitedTokenMap(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__13;
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPosFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo___elambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__23;
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_strLitNoAntiquot___closed__3;
static lean_object* l_Lean_Parser_manyAux___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_parserOfStackFnUnsafe___closed__5;
static lean_object* l_Lean_Parser_charLitNoAntiquot___closed__1;
static lean_object* l_Lean_Parser_mkAntiquotSplice___closed__5;
static lean_object* l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_quotDepth___default;
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailNoWs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___elambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkOutsideQuot;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_anyOfFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkEmptySubstringAt(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_anyOfFn___closed__1;
static lean_object* l_Lean_Parser_Error_toString___closed__2;
extern lean_object* l_Lean_instInhabitedSyntax;
LEAN_EXPORT lean_object* l_Lean_Parser_checkInsideQuot;
static lean_object* l_Lean_Parser_identFnAux_parse___lambda__2___closed__1;
static lean_object* l_Lean_Parser_nameLitNoAntiquot___closed__3;
static lean_object* l_Lean_Parser_evalParserConstUnsafe___closed__5;
static lean_object* l_Lean_Parser_evalParserConstUnsafe___closed__7;
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instReprLeadingIdentBehavior___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh(uint32_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo___elambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_quotedCharCoreFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_identFnAux_parse___lambda__2___closed__2;
static lean_object* l_Lean_Parser_mkAntiquot___closed__21;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_Parser_charLitNoAntiquot___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_termParser(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_FirstTokens_toStr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Parser_checkInsideQuotFn___closed__1;
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__7;
static lean_object* l_Lean_Parser_pushNone___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_chFn(uint32_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo___elambda__2___boxed(lean_object*);
static lean_object* l_Lean_Parser_mkAntiquotSplice___closed__8;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString___closed__2;
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Parser_dbgTraceStateFn___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_instToStringFirstTokens;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon;
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_scientificLitNoAntiquot___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_addQuotDepthFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_rawIdentNoAntiquot___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___elambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkOutsideQuotFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux_parse___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy___elambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_checkInsideQuot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEqFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateCache(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lambda__1___boxed(lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParser___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_quotedCharFn___closed__1;
static lean_object* l_Lean_Parser_charLitFnAux___closed__1;
static lean_object* l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkInsideQuotFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNode(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_scientificLitNoAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo___elambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_checkInsideQuot___closed__2;
static lean_object* l_Lean_Parser_pushNone___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1(lean_object*);
static lean_object* l_Lean_Parser_tokenWithAntiquotFn___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo___elambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Parser_info___default___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGeFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFnAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_evalParserConstUnsafe___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_identKind;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_fieldIdxFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol___boxed(lean_object*);
static lean_object* l_Lean_Parser_scientificLitNoAntiquot___closed__4;
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___lambda__1(lean_object*);
static lean_object* l_Lean_Parser_charLitFn___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn(lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__16;
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___elambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLitNoAntiquot;
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___rarg(lean_object*);
static lean_object* l_Lean_Parser_instInhabitedInputContext___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Error_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserOfStackFn___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_checkNoImmediateColon___elambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquotSplice___closed__6;
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
static lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquotFn___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___at_Lean_Syntax_forArgsM___spec__2___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_scientificLitKind;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_tokenWithAntiquotFn___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_PrattParsingTables_trailingTable___default;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserModuleContext_currNamespace___default;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__24;
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Parser_dbgTraceStateFn___closed__6;
static lean_object* l_Lean_Parser_decQuotDepth___closed__1;
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_numLitNoAntiquot___closed__3;
static lean_object* l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Parser_info___default___elambda__2___boxed(lean_object*);
uint8_t l_Std_RBNode_isRed___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth(lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__6;
static lean_object* l_Lean_Parser_mkAntiquot___closed__22;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1NoAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenCacheEntry_token___default;
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_numLitNoAntiquot;
static lean_object* l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__2;
static lean_object* l_Lean_Parser_Error_instToStringError___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollectionTokenMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7242_(uint8_t, uint8_t);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos(lean_object*, uint8_t);
static lean_object* l_Lean_Parser_mkAntiquot___closed__14;
static lean_object* l_Lean_Parser_FirstTokens_toStr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn___lambda__1(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutInfo___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserModuleContext_openDecls___default;
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addQuotDepthFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo(lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__15;
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTop(lean_object*, lean_object*);
lean_object* l_String_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedPrattParsingTables;
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo;
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1(lean_object*);
static lean_object* l_Lean_Parser_epsilonInfo___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquotFn___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParser;
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___elambda__1(lean_object*);
static lean_object* l_Lean_Parser_FirstTokens_toStr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentNoAntiquot;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdxFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqError;
static lean_object* l_Lean_Parser_mkAntiquot___closed__19;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_UInt32_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptDot___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_unicodeSymbolFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_forbiddenTk_x3f___default;
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_PrattParsingTables_trailingParsers___default;
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo___elambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___at_Lean_Syntax_forArgsM___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_nameLitFn___closed__2;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tryAnti___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedFirstTokens;
static lean_object* l_Lean_Parser_epsilonInfo___closed__2;
LEAN_EXPORT uint8_t l_Lean_Parser_tryAnti___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_numberFnAux___closed__1;
static lean_object* l_Lean_Parser_nonReservedSymbolInfo___closed__1;
LEAN_EXPORT lean_object* l_List_eraseReps___at_Lean_Parser_Error_toString___spec__3(lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParser___closed__2;
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isIdCont___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhile1Fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_identNoAntiquot___closed__3;
static lean_object* l_Lean_Parser_epsilonInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrec(lean_object*);
static lean_object* l_Lean_Parser_checkNoImmediateColon___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___rarg(lean_object*);
static lean_object* l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_Parser_info___default___elambda__2(lean_object*);
lean_object* l_String_trim(lean_object*);
lean_object* l_Lean_isIdEndEscape___boxed(lean_object*);
static lean_object* l_Lean_Parser_parserOfStackFnUnsafe___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_lhsPrec___default;
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_charLitFn___closed__1;
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParserInfo___closed__2;
static lean_object* l_Lean_Parser_instInhabitedInputContext___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_nodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_pos___default;
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optionalFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_nameLitFn___closed__1;
static lean_object* l_Lean_Parser_checkOutsideQuotFn___closed__1;
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkOutsideQuotFn___boxed(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_nonReservedSymbolInfo___closed__4;
static lean_object* l_Lean_Parser_instInhabitedInputContext___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_strAux_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_evalParserConstUnsafe___closed__2;
uint8_t l_Lean_isIdFirst(uint32_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_chFn___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_mkTokenAndFixPos___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhile1Fn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_charLitFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFnUnsafe___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo___elambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt(lean_object*);
static lean_object* l_Lean_Parser_symbolInfo___closed__1;
static lean_object* l_Lean_Parser_mkAntiquot___closed__6;
static lean_object* l_Lean_Parser_parserOfStackFnUnsafe___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7595_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7614_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755_(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_instInhabitedLeadingIdentBehavior;
static lean_object* l_Lean_Parser_fieldIdx___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Parser_instBEqLeadingIdentBehavior___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_optionaInfo___elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserInfo_collectTokens___default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_evalParserConstUnsafe___closed__1;
static lean_object* l_Lean_Parser_eoiFn___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqError____x40_Lean_Parser_Basic___hyg_353_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7(lean_object*);
static lean_object* l_Lean_Parser_mkAtomicInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGtFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Error_toString___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdx;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___elambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_categoryParserOfStackFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_manyFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__11;
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info___elambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___elambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrec(lean_object*);
static lean_object* l_Lean_Parser_numLitFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___at_Lean_Syntax_forArgsM___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___elambda__1(lean_object*);
lean_object* l_IO_mkRef___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnExtension;
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock_eoi(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___elambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo___elambda__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_node(lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__17;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__8;
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identNoAntiquot;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot(lean_object*, lean_object*);
lean_object* l_Nat_min(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquotSplice___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParser(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParser___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo___elambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object*);
static lean_object* l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailLinebreak___boxed(lean_object*);
uint8_t l_UInt32_decLe(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_ParserState_hasError(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_hexDigitFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtom(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_pushNone___elambda__1___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7614____lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserOfStackFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__25;
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1___elambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenCacheEntry_stopPos___default;
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected___elambda__1(lean_object*);
static lean_object* l_Lean_Parser_unicodeSymbolInfo___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___lambda__1___boxed(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Error_toString___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserOfStack___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qpartition_loop___at_Lean_Parser_Error_toString___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_charLitNoAntiquot;
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGtFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2(lean_object*);
static lean_object* l_Lean_Parser_mkAtomicInfo___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__4;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__12;
static lean_object* l_Lean_Parser_identNoAntiquot___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden(lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdxFn(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_hexNumberFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdent(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isLitKind___boxed(lean_object*);
static lean_object* l_Lean_Parser_mkAntiquotSplice___closed__10;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instBEqName;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_error(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toStringAux___at_Lean_Parser_FirstTokens_toStr___spec__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Char_isDigit___boxed(lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stxStack___default;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isLitKind(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_isLitKind___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_isLitKind(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT uint32_t l_Lean_Parser_getNext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; 
x_3 = lean_string_utf8_next(x_1, x_2);
x_4 = lean_string_utf8_get(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getNext___boxed(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lean_Parser_argPrec() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1023u);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_leadPrec() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1022u);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_minPrec() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(10u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_initCacheForInput(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxNodeKindSet_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Name_instBEqName;
x_4 = l_Lean_instHashableName;
x_5 = lean_box(0);
x_6 = l_Std_PersistentHashMap_insert___rarg(x_3, x_4, x_1, x_2, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_2 = l_Lean_Parser_instInhabitedInputContext___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_2 = l_Lean_Parser_instInhabitedInputContext___closed__3;
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
x_1 = l_Lean_Parser_instInhabitedInputContext___closed__4;
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
static lean_object* _init_l_Lean_Parser_ParserContext_quotDepth___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveName(lean_object* x_1, lean_object* x_2) {
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
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_Error_unexpected___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instInhabitedInputContext___closed__2;
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
x_2 = l_Lean_Parser_instInhabitedInputContext___closed__2;
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
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqError____x40_Lean_Parser_Basic___hyg_353_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_string_dec_eq(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = l_List_beq___at_Lean_Syntax_structEq___spec__3(x_4, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqError____x40_Lean_Parser_Basic___hyg_353____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Parser_Basic_0__Lean_Parser_beqError____x40_Lean_Parser_Basic___hyg_353_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_instBEqError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_beqError____x40_Lean_Parser_Basic___hyg_353____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instBEqError() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instBEqError___closed__1;
return x_1;
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
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", ");
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instInhabitedInputContext___closed__2;
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
x_12 = l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString___closed__2;
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
LEAN_EXPORT lean_object* l_Array_qpartition_loop___at_Lean_Parser_Error_toString___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_List_eraseRepsAux___at_Lean_Parser_Error_toString___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_List_eraseReps___at_Lean_Parser_Error_toString___spec__3(lean_object* x_1) {
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
x_2 = l_List_appendTR___rarg(x_1, x_1);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Error_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Parser_instInhabitedInputContext___closed__2;
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
x_23 = l_List_appendTR___rarg(x_8, x_22);
x_24 = l_Lean_Parser_Error_toString___closed__2;
x_25 = l_String_intercalate(x_24, x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
x_26 = l_List_appendTR___rarg(x_8, x_6);
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
x_43 = l_List_appendTR___rarg(x_6, x_42);
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
LEAN_EXPORT lean_object* l_Array_qpartition_loop___at_Lean_Parser_Error_toString___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qpartition_loop___at_Lean_Parser_Error_toString___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Parser_Error_toString___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_Error_merge(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_6 = lean_string_dec_eq(x_3, x_5);
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_List_appendTR___rarg(x_9, x_4);
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
x_13 = l_List_appendTR___rarg(x_12, x_4);
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
x_1 = l_Lean_Parser_instInhabitedInputContext___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_lhsPrec___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_8 = l___private_Lean_Parser_Basic_0__Lean_Parser_beqError____x40_Lean_Parser_Basic___hyg_353_(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_ParserState_hasError(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 4);
x_3 = lean_box(0);
x_4 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_2, x_3);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_ParserState_hasError(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ParserState_stackSize(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 4);
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_dec(x_7);
x_8 = l_Array_shrink___rarg(x_5, x_2);
x_9 = lean_box(0);
lean_ctor_set(x_1, 4, x_9);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_13 = l_Array_shrink___rarg(x_10, x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_restore(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setPos(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setCache(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_dec(x_4);
lean_ctor_set(x_1, 3, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_2);
lean_ctor_set(x_9, 4, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_11 = lean_array_push(x_6, x_2);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object* x_1) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_10 = lean_array_pop(x_5);
x_11 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_7);
lean_ctor_set(x_11, 3, x_8);
lean_ctor_set(x_11, 4, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_11 = l_Array_shrink___rarg(x_6, x_2);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_shrinkStack(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 2);
lean_dec(x_5);
x_6 = lean_string_utf8_next(x_2, x_3);
lean_ctor_set(x_1, 2, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_11 = lean_string_utf8_next(x_2, x_3);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_next(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = l_Lean_Parser_instInhabitedInputContext___closed__2;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_6, 2);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_FileMap_toPosition(x_7, x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_6, 1);
x_11 = l_Lean_Parser_Error_toString(x_5);
x_12 = lean_box(0);
x_13 = l_Lean_mkErrorStringWithPos(x_10, x_9, x_11, x_12);
lean_dec(x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_toErrorMsg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_5);
x_10 = lean_nat_dec_eq(x_9, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_3);
lean_inc(x_5);
x_11 = l_Array_extract___rarg(x_5, x_3, x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Array_shrink___rarg(x_5, x_3);
lean_dec(x_3);
x_14 = lean_array_push(x_13, x_12);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_array_push(x_5, x_15);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_array_get_size(x_5);
lean_inc(x_3);
lean_inc(x_5);
x_18 = l_Array_extract___rarg(x_5, x_3, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Array_shrink___rarg(x_5, x_3);
lean_dec(x_3);
x_21 = lean_array_push(x_20, x_19);
lean_ctor_set(x_1, 0, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_1, 2);
x_25 = lean_ctor_get(x_1, 3);
x_26 = lean_ctor_get(x_1, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_array_get_size(x_22);
x_30 = lean_nat_dec_eq(x_29, x_3);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_3);
lean_inc(x_22);
x_31 = l_Array_extract___rarg(x_22, x_3, x_29);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Array_shrink___rarg(x_22, x_3);
lean_dec(x_3);
x_34 = lean_array_push(x_33, x_32);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_23);
lean_ctor_set(x_35, 2, x_24);
lean_ctor_set(x_35, 3, x_25);
lean_ctor_set(x_35, 4, x_26);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = lean_array_push(x_22, x_36);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_38, 2, x_24);
lean_ctor_set(x_38, 3, x_25);
lean_ctor_set(x_38, 4, x_26);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_array_get_size(x_22);
lean_inc(x_3);
lean_inc(x_22);
x_40 = l_Array_extract___rarg(x_22, x_3, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Array_shrink___rarg(x_22, x_3);
lean_dec(x_3);
x_43 = lean_array_push(x_42, x_41);
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_23);
lean_ctor_set(x_44, 2, x_24);
lean_ctor_set(x_44, 3, x_25);
lean_ctor_set(x_44, 4, x_26);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_inc(x_7);
lean_inc(x_5);
x_9 = l_Array_extract___rarg(x_5, x_7, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Array_shrink___rarg(x_5, x_7);
lean_dec(x_7);
x_12 = lean_array_push(x_11, x_10);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get(x_1, 3);
x_17 = lean_ctor_get(x_1, 4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_3, x_18);
x_20 = lean_array_get_size(x_13);
lean_inc(x_19);
lean_inc(x_13);
x_21 = l_Array_extract___rarg(x_13, x_19, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Array_shrink___rarg(x_13, x_19);
lean_dec(x_19);
x_24 = lean_array_push(x_23, x_22);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_14);
lean_ctor_set(x_25, 2, x_15);
lean_ctor_set(x_25, 3, x_16);
lean_ctor_set(x_25, 4, x_17);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_mkTrailingNode(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setError(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 4);
lean_dec(x_4);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_1, 4, x_9);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_19, 3, x_13);
lean_ctor_set(x_19, 4, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkError(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 4);
lean_dec(x_5);
x_6 = lean_box(0);
x_7 = lean_array_push(x_4, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_1, 4, x_12);
lean_ctor_set(x_1, 0, x_7);
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
x_17 = lean_box(0);
x_18 = lean_array_push(x_13, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_14);
lean_ctor_set(x_24, 2, x_15);
lean_ctor_set(x_24, 3, x_16);
lean_ctor_set(x_24, 4, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 4);
lean_dec(x_6);
x_7 = lean_box(0);
x_8 = lean_array_push(x_5, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_1, 4, x_10);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_array_push(x_11, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_19, 2, x_13);
lean_ctor_set(x_19, 3, x_14);
lean_ctor_set(x_19, 4, x_18);
return x_19;
}
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkEOIError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected end of input");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_4 = l_Lean_Parser_ParserState_mkUnexpectedError(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 4);
lean_dec(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_dec(x_8);
x_9 = lean_box(0);
x_10 = lean_array_push(x_6, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_1, 4, x_15);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_array_push(x_16, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_17);
lean_ctor_set(x_26, 2, x_3);
lean_ctor_set(x_26, 3, x_18);
lean_ctor_set(x_26, 4, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 4);
lean_dec(x_29);
x_30 = lean_ctor_get(x_1, 2);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_4);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_4, 0);
x_33 = l_Array_shrink___rarg(x_28, x_32);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = lean_array_push(x_33, x_34);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_4, 0, x_39);
lean_ctor_set(x_1, 4, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 0, x_35);
return x_1;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_4, 0);
lean_inc(x_40);
lean_dec(x_4);
x_41 = l_Array_shrink___rarg(x_28, x_40);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = lean_array_push(x_41, x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_2);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_1, 4, x_48);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 0, x_43);
return x_1;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_49 = lean_ctor_get(x_1, 0);
x_50 = lean_ctor_get(x_1, 1);
x_51 = lean_ctor_get(x_1, 3);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_1);
x_52 = lean_ctor_get(x_4, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_53 = x_4;
} else {
 lean_dec_ref(x_4);
 x_53 = lean_box(0);
}
x_54 = l_Array_shrink___rarg(x_49, x_52);
lean_dec(x_52);
x_55 = lean_box(0);
x_56 = lean_array_push(x_54, x_55);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_2);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
if (lean_is_scalar(x_53)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_53;
}
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_50);
lean_ctor_set(x_62, 2, x_3);
lean_ctor_set(x_62, 3, x_51);
lean_ctor_set(x_62, 4, x_61);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 4);
lean_dec(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_dec(x_8);
x_9 = lean_box(0);
x_10 = lean_array_push(x_6, x_9);
x_11 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_1, 4, x_13);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_array_push(x_14, x_17);
x_19 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_22, 2, x_3);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 4);
lean_dec(x_25);
x_26 = lean_ctor_get(x_1, 2);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = l_Array_shrink___rarg(x_24, x_28);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = lean_array_push(x_29, x_30);
x_32 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_2);
lean_ctor_set(x_4, 0, x_33);
lean_ctor_set(x_1, 4, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_4, 0);
lean_inc(x_34);
lean_dec(x_4);
x_35 = l_Array_shrink___rarg(x_24, x_34);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = lean_array_push(x_35, x_36);
x_38 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_2);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_1, 4, x_40);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 0, x_37);
return x_1;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
x_43 = lean_ctor_get(x_1, 3);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_1);
x_44 = lean_ctor_get(x_4, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_45 = x_4;
} else {
 lean_dec_ref(x_4);
 x_45 = lean_box(0);
}
x_46 = l_Array_shrink___rarg(x_41, x_44);
lean_dec(x_44);
x_47 = lean_box(0);
x_48 = lean_array_push(x_46, x_47);
x_49 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_2);
if (lean_is_scalar(x_45)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_45;
}
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_42);
lean_ctor_set(x_52, 2, x_3);
lean_ctor_set(x_52, 3, x_43);
lean_ctor_set(x_52, 4, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 4);
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_dec(x_7);
x_8 = lean_box(0);
x_9 = lean_array_push(x_5, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_1, 4, x_12);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_array_push(x_13, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_3);
lean_ctor_set(x_21, 3, x_15);
lean_ctor_set(x_21, 4, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_instInhabitedParserFn___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instInhabitedParserFn___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_seq(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_List_appendTR___rarg(x_3, x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_List_appendTR___rarg(x_3, x_7);
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
x_13 = l_List_appendTR___rarg(x_10, x_12);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_List_appendTR___rarg(x_10, x_14);
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
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_merge(lean_object* x_1, lean_object* x_2) {
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
x_11 = l_List_appendTR___rarg(x_8, x_10);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_List_appendTR___rarg(x_8, x_12);
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
x_18 = l_List_appendTR___rarg(x_15, x_17);
lean_ctor_set(x_2, 0, x_18);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l_List_appendTR___rarg(x_15, x_19);
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
x_27 = l_List_appendTR___rarg(x_24, x_26);
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
x_29 = l_List_appendTR___rarg(x_24, x_28);
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
x_34 = l_List_appendTR___rarg(x_31, x_33);
lean_ctor_set(x_2, 0, x_34);
return x_2;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_2, 0);
lean_inc(x_35);
lean_dec(x_2);
x_36 = l_List_appendTR___rarg(x_31, x_35);
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
LEAN_EXPORT lean_object* l_List_toStringAux___at_Lean_Parser_FirstTokens_toStr___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Lean_Parser_instInhabitedInputContext___closed__2;
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
x_6 = l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString___closed__2;
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
x_11 = l_Lean_Parser_instInhabitedInputContext___closed__2;
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
static lean_object* _init_l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[]");
return x_1;
}
}
static lean_object* _init_l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
static lean_object* _init_l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]");
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__1;
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
x_6 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__2;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__3;
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
x_15 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__2;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__3;
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
static lean_object* _init_l_Lean_Parser_FirstTokens_toStr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("?");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object* x_1) {
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
x_8 = l_Lean_Parser_FirstTokens_toStr___closed__3;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toStringAux___at_Lean_Parser_FirstTokens_toStr___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserInfo_collectTokens___default(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserInfo_collectTokens___default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_ParserInfo_collectTokens___default(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserInfo_collectKinds___default(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserInfo_collectKinds___default___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instInhabitedParserInfo___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instInhabitedParserInfo___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Parser_info___default___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Parser_info___default___elambda__2(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_Parser_info___default___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Parser_info___default___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Parser_info___default___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Parser_info___default___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParser___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParser___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_instInhabitedParser___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toStringAux___at_Lean_Parser_dbgTraceStateFn___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Lean_Parser_instInhabitedInputContext___closed__2;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = 0;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_formatStxAux(x_6, x_7, x_8, x_4);
x_10 = l_Std_Format_defWidth;
x_11 = lean_format_pretty(x_9, x_10);
x_12 = l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_List_toStringAux___at_Lean_Parser_dbgTraceStateFn___spec__2(x_7, x_5);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
return x_15;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Parser_instInhabitedInputContext___closed__2;
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = 0;
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_formatStxAux(x_19, x_20, x_21, x_17);
x_23 = l_Std_Format_defWidth;
x_24 = lean_format_pretty(x_22, x_23);
x_25 = l_List_toStringAux___at_Lean_Parser_dbgTraceStateFn___spec__2(x_20, x_18);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Parser_dbgTraceStateFn___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__1;
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
x_5 = l_List_toStringAux___at_Lean_Parser_dbgTraceStateFn___spec__2(x_4, x_1);
x_6 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__2;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__3;
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
x_14 = l_List_toStringAux___at_Lean_Parser_dbgTraceStateFn___spec__2(x_13, x_12);
x_15 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__2;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__3;
x_18 = lean_string_append(x_16, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_dbgTraceStateFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n  pos: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_dbgTraceStateFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n  err: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_dbgTraceStateFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_dbgTraceStateFn___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("none");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_dbgTraceStateFn___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n  out: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_dbgTraceStateFn___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(some ");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_dbgTraceStateFn___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_7 = lean_apply_2(x_2, x_3, x_4);
x_8 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_9 = lean_string_append(x_8, x_1);
x_10 = l_Lean_Parser_dbgTraceStateFn___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
x_13 = l_Nat_repr(x_12);
x_14 = lean_string_append(x_11, x_13);
lean_dec(x_13);
x_15 = l_Lean_Parser_dbgTraceStateFn___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_ctor_get(x_7, 4);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
x_19 = lean_array_get_size(x_18);
x_20 = l_Array_extract___rarg(x_18, x_6, x_19);
x_21 = lean_array_to_list(lean_box(0), x_20);
x_22 = l_List_toString___at_Lean_Parser_dbgTraceStateFn___spec__1(x_21);
x_23 = l_Lean_Parser_dbgTraceStateFn___closed__3;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_dbgTraceStateFn___lambda__1___boxed), 2, 1);
lean_closure_set(x_25, 0, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = l_Lean_Parser_dbgTraceStateFn___closed__4;
x_27 = lean_string_append(x_16, x_26);
x_28 = l_Lean_Parser_dbgTraceStateFn___closed__5;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_string_append(x_29, x_24);
lean_dec(x_24);
x_31 = lean_string_append(x_30, x_8);
x_32 = lean_dbg_trace(x_31, x_25);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
lean_dec(x_17);
x_34 = l_Lean_Parser_Error_toString(x_33);
x_35 = l_addParenHeuristic(x_34);
lean_dec(x_34);
x_36 = l_Lean_Parser_dbgTraceStateFn___closed__6;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Lean_Parser_dbgTraceStateFn___closed__7;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_string_append(x_16, x_39);
lean_dec(x_39);
x_41 = l_Lean_Parser_dbgTraceStateFn___closed__5;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_string_append(x_42, x_24);
lean_dec(x_24);
x_44 = lean_string_append(x_43, x_8);
x_45 = lean_dbg_trace(x_44, x_25);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_List_toStringAux___at_Lean_Parser_dbgTraceStateFn___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___at_Lean_Parser_dbgTraceStateFn___spec__2(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_dbgTraceStateFn___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_dbgTraceStateFn(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_dbgTraceStateFn(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_dbgTraceState___elambda__1___boxed), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
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
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_dbgTraceState___elambda__1___boxed), 4, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_dbgTraceState___elambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___elambda__2(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_epsilonInfo___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_epsilonInfo___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTopFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_2, x_9);
return x_10;
}
else
{
lean_dec(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTopFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_checkStackTopFn(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTop(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_andthenFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_andthen(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_instAndThenParser(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = l_Lean_Parser_andthenInfo(x_5, x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_3);
x_6 = l_Lean_Name_instBEqName;
x_7 = l_Lean_instHashableName;
x_8 = lean_box(0);
x_9 = l_Std_PersistentHashMap_insert___rarg(x_6, x_7, x_5, x_1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo___elambda__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_node(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_errorFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_error(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPosFn(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 5);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 4);
lean_dec(x_10);
x_11 = lean_ctor_get(x_4, 2);
lean_dec(x_11);
x_12 = lean_box(0);
x_13 = lean_array_push(x_9, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_5, 0, x_15);
lean_ctor_set(x_4, 4, x_5);
lean_ctor_set(x_4, 2, x_8);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_4, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = lean_array_push(x_17, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_5, 0, x_23);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_16);
lean_ctor_set(x_24, 3, x_19);
lean_ctor_set(x_24, 4, x_5);
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
x_28 = lean_ctor_get(x_4, 3);
lean_inc(x_28);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_29 = x_4;
} else {
 lean_dec_ref(x_4);
 x_29 = lean_box(0);
}
x_30 = lean_box(0);
x_31 = lean_array_push(x_26, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
if (lean_is_scalar(x_29)) {
 x_35 = lean_alloc_ctor(0, 5, 0);
} else {
 x_35 = x_29;
}
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_27);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_28);
lean_ctor_set(x_35, 4, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_5);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_5, 0);
x_38 = lean_ctor_get(x_3, 0);
lean_inc(x_38);
lean_dec(x_3);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_string_utf8_next(x_39, x_37);
lean_dec(x_37);
lean_dec(x_39);
x_41 = !lean_is_exclusive(x_4);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_4, 0);
x_43 = lean_ctor_get(x_4, 4);
lean_dec(x_43);
x_44 = lean_ctor_get(x_4, 2);
lean_dec(x_44);
x_45 = lean_box(0);
x_46 = lean_array_push(x_42, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_5, 0, x_48);
lean_ctor_set(x_4, 4, x_5);
lean_ctor_set(x_4, 2, x_40);
lean_ctor_set(x_4, 0, x_46);
return x_4;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_4, 0);
x_50 = lean_ctor_get(x_4, 1);
x_51 = lean_ctor_get(x_4, 3);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_4);
x_52 = lean_box(0);
x_53 = lean_array_push(x_49, x_52);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_5, 0, x_55);
x_56 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_50);
lean_ctor_set(x_56, 2, x_40);
lean_ctor_set(x_56, 3, x_51);
lean_ctor_set(x_56, 4, x_5);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_57 = lean_ctor_get(x_5, 0);
lean_inc(x_57);
lean_dec(x_5);
x_58 = lean_ctor_get(x_3, 0);
lean_inc(x_58);
lean_dec(x_3);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_string_utf8_next(x_59, x_57);
lean_dec(x_57);
lean_dec(x_59);
x_61 = lean_ctor_get(x_4, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_4, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_4, 3);
lean_inc(x_63);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_64 = x_4;
} else {
 lean_dec_ref(x_4);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
x_66 = lean_array_push(x_61, x_65);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
if (lean_is_scalar(x_64)) {
 x_70 = lean_alloc_ctor(0, 5, 0);
} else {
 x_70 = x_64;
}
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_62);
lean_ctor_set(x_70, 2, x_60);
lean_ctor_set(x_70, 3, x_63);
lean_ctor_set(x_70, 4, x_69);
return x_70;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPosFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_errorAtSavedPos___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_errorAtSavedPos___closed__1;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_errorAtSavedPosFn___boxed), 4, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = l_Lean_Parser_errorAtSavedPos___closed__2;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrecFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_nat_dec_le(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = l_Lean_Parser_checkPrecFn___closed__1;
x_8 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_7, x_6);
return x_8;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrecFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkPrecFn(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrec(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_nat_dec_le(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = l_Lean_Parser_checkPrecFn___closed__1;
x_8 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_7, x_6);
return x_8;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkLhsPrecFn(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrec(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkLhsPrecFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_epsilonInfo;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 4);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_3, 4);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_3, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_3, 0);
lean_dec(x_15);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_16, 2, x_5);
lean_ctor_set(x_16, 3, x_6);
lean_ctor_set(x_16, 4, x_7);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_setLhsPrecFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrec(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_setLhsPrecFn___boxed), 3, 1);
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
LEAN_EXPORT lean_object* l_Lean_Parser_checkInsideQuotFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 4);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = l_Lean_Parser_checkInsideQuotFn___closed__1;
x_8 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_7, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
if (x_9 == 0)
{
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(0);
x_11 = l_Lean_Parser_checkInsideQuotFn___closed__1;
x_12 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_11, x_10);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkInsideQuotFn___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_checkOutsideQuotFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 4);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = l_Lean_Parser_checkOutsideQuotFn___closed__1;
x_9 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_8, x_7);
return x_9;
}
else
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkOutsideQuotFn___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_addQuotDepthFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 4);
x_7 = lean_nat_to_int(x_6);
x_8 = lean_int_add(x_7, x_1);
lean_dec(x_7);
x_9 = l_Int_toNat(x_8);
lean_dec(x_8);
lean_ctor_set(x_3, 4, x_9);
x_10 = lean_apply_2(x_2, x_3, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
x_14 = lean_ctor_get(x_3, 3);
x_15 = lean_ctor_get(x_3, 4);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_17 = lean_ctor_get(x_3, 5);
x_18 = lean_ctor_get(x_3, 6);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_19 = lean_nat_to_int(x_15);
x_20 = lean_int_add(x_19, x_1);
lean_dec(x_19);
x_21 = l_Int_toNat(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_21);
lean_ctor_set(x_22, 5, x_17);
lean_ctor_set(x_22, 6, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*7, x_16);
x_23 = lean_apply_2(x_2, x_22, x_4);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addQuotDepthFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_addQuotDepthFn(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_incQuotDepth___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Parser_incQuotDepth___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_addQuotDepthFn___boxed), 4, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
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
x_8 = l_Lean_Parser_incQuotDepth___closed__1;
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_addQuotDepthFn___boxed), 4, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
static lean_object* _init_l_Lean_Parser_decQuotDepth___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_incQuotDepth___closed__1;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Parser_decQuotDepth___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_addQuotDepthFn___boxed), 4, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
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
x_8 = l_Lean_Parser_decQuotDepth___closed__1;
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_addQuotDepthFn___boxed), 4, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuotFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
lean_ctor_set_uint8(x_2, sizeof(void*)*7, x_5);
x_6 = lean_apply_2(x_1, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_14 = 1;
x_15 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_8);
lean_ctor_set(x_15, 2, x_9);
lean_ctor_set(x_15, 3, x_10);
lean_ctor_set(x_15, 4, x_11);
lean_ctor_set(x_15, 5, x_12);
lean_ctor_set(x_15, 6, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*7, x_14);
x_16 = lean_apply_2(x_1, x_15, x_3);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_2);
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
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_setLhsPrecFn___boxed), 3, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = l_Lean_Parser_epsilonInfo;
x_11 = l_Lean_Parser_andthenInfo(x_6, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_9);
x_13 = l_Lean_Parser_andthenInfo(x_10, x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeAux(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_checkPrecFn___boxed), 3, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_checkLhsPrecFn___boxed), 3, 1);
lean_closure_set(x_6, 0, x_3);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_inc(x_1);
x_8 = l_Lean_Parser_nodeInfo(x_1, x_7);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_trailingNodeFn), 4, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_setLhsPrecFn___boxed), 3, 1);
lean_closure_set(x_11, 0, x_2);
x_12 = l_Lean_Parser_epsilonInfo;
x_13 = l_Lean_Parser_andthenInfo(x_8, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_11);
x_15 = l_Lean_Parser_andthenInfo(x_12, x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_16, 0, x_6);
lean_closure_set(x_16, 1, x_14);
x_17 = l_Lean_Parser_andthenInfo(x_12, x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_18, 0, x_5);
lean_closure_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_nat_dec_eq(x_8, x_3);
if (x_12 == 0)
{
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_1, 4);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 3);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 0);
lean_dec(x_18);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_Parser_Error_merge(x_2, x_11);
lean_ctor_set(x_5, 0, x_19);
return x_1;
}
}
else
{
lean_dec(x_1);
if (x_4 == 0)
{
lean_object* x_20; 
lean_dec(x_2);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_7);
lean_ctor_set(x_20, 2, x_8);
lean_ctor_set(x_20, 3, x_9);
lean_ctor_set(x_20, 4, x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Parser_Error_merge(x_2, x_11);
lean_ctor_set(x_5, 0, x_21);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_7);
lean_ctor_set(x_22, 2, x_8);
lean_ctor_set(x_22, 3, x_9);
lean_ctor_set(x_22, 4, x_5);
return x_22;
}
}
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
lean_dec(x_5);
x_24 = lean_nat_dec_eq(x_8, x_3);
if (x_24 == 0)
{
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_25; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 x_25 = x_1;
} else {
 lean_dec_ref(x_1);
 x_25 = lean_box(0);
}
if (x_4 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 5, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_7);
lean_ctor_set(x_27, 2, x_8);
lean_ctor_set(x_27, 3, x_9);
lean_ctor_set(x_27, 4, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = l_Lean_Parser_Error_merge(x_2, x_23);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
if (lean_is_scalar(x_25)) {
 x_30 = lean_alloc_ctor(0, 5, 0);
} else {
 x_30 = x_25;
}
lean_ctor_set(x_30, 0, x_6);
lean_ctor_set(x_30, 1, x_7);
lean_ctor_set(x_30, 2, x_8);
lean_ctor_set(x_30, 3, x_9);
lean_ctor_set(x_30, 4, x_29);
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mergeOrElseErrors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
lean_inc(x_4);
x_9 = lean_apply_2(x_1, x_4, x_5);
x_10 = lean_ctor_get(x_9, 4);
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
x_12 = lean_ctor_get(x_9, 2);
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
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Parser_orelseFnCore(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
x_6 = l_Lean_Parser_orelseFnCore(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_orelse(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParser(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = l_Lean_Parser_orelseInfo(x_5, x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn), 4, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo___elambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo___elambda__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_atomicFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = lean_apply_2(x_1, x_2, x_3);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 4);
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_5, 4, x_12);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_17 = x_6;
} else {
 lean_dec_ref(x_6);
 x_17 = lean_box(0);
}
if (lean_is_scalar(x_17)) {
 x_18 = lean_alloc_ctor(1, 1, 0);
} else {
 x_18 = x_17;
}
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_4);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomic(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_optionalFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_apply_2(x_1, x_2, x_3);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_7, 2);
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
LEAN_EXPORT lean_object* l_Lean_Parser_optionaInfo___elambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_optionaInfo___elambda__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_optionaInfo(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_lookaheadFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_apply_2(x_1, x_2, x_3);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_apply_2(x_1, x_3, x_4);
x_9 = lean_ctor_get(x_8, 4);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_9, x_10);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
lean_dec(x_6);
x_14 = l_Lean_Parser_notFollowedByFn___closed__1;
x_15 = lean_string_append(x_14, x_2);
x_16 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_box(0);
x_19 = l_Lean_Parser_ParserState_mkUnexpectedError(x_13, x_17, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_notFollowedByFn(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByFn___boxed), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Lean_Parser_errorAtSavedPos___closed__2;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_manyAux(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_nat_dec_lt(x_7, x_9);
lean_dec(x_9);
lean_dec(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = l_Lean_Parser_manyAux(x_1, x_2, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_nullKind;
x_13 = l_Lean_Parser_ParserState_mkNode(x_4, x_12, x_3);
x_14 = l_Lean_Parser_manyAux(x_1, x_2, x_13);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Parser_manyAux___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'many' parser combinator application, parser did not consume anything");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
x_8 = lean_nat_dec_eq(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Parser_manyAux___lambda__2(x_1, x_2, x_3, x_5, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_Parser_manyAux___lambda__3___closed__1;
x_13 = l_Lean_Parser_ParserState_mkUnexpectedError(x_5, x_12, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_2);
x_7 = lean_apply_2(x_1, x_2, x_3);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_ctor_get(x_7, 2);
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
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Parser_manyAux___lambda__3(x_1, x_2, x_5, x_6, x_7, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_manyAux___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_manyAux___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_manyAux___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_manyNoAntiquot(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_many1Fn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Parser_many1NoAntiquot(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_dec(x_7);
x_8 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(x_1, x_2, x_3, x_4, x_3, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_6, x_9);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
x_13 = lean_nat_dec_lt(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_6);
x_14 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(x_1, x_2, x_3, x_4, x_3, x_5, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_nullKind;
x_16 = l_Lean_Parser_ParserState_mkNode(x_7, x_15, x_6);
x_17 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(x_1, x_2, x_3, x_4, x_3, x_5, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_6, 2);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_2);
x_11 = lean_apply_2(x_1, x_2, x_6);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Parser_ParserState_restore(x_11, x_9, x_10);
lean_dec(x_9);
x_16 = l_Lean_nullKind;
x_17 = l_Lean_Parser_ParserState_mkNode(x_15, x_16, x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
x_18 = lean_box(0);
x_19 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__2(x_3, x_1, x_4, x_5, x_2, x_9, x_11, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_6, x_9);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
x_13 = lean_nat_dec_lt(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_14 = lean_box(0);
x_15 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__3(x_1, x_2, x_3, x_4, x_5, x_7, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_nullKind;
x_17 = l_Lean_Parser_ParserState_mkNode(x_7, x_16, x_6);
x_18 = lean_box(0);
x_19 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__3(x_1, x_2, x_3, x_4, x_5, x_17, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_6);
x_11 = lean_apply_2(x_1, x_6, x_7);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_11, 2);
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
lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
x_24 = l_Lean_nullKind;
x_25 = l_Lean_Parser_ParserState_mkNode(x_11, x_24, x_4);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
x_26 = lean_box(0);
x_27 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__4(x_2, x_6, x_1, x_3, x_4, x_9, x_11, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__1(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__2(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__3(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__4(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Parser_sepByFn(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Parser_sepBy1Fn(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Parser_sepByNoAntiquot(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Parser_sepBy1NoAntiquot(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo___elambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo___elambda__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOf(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lambda__1(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_many1Unbox___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 2);
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
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_2, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = l_Lean_Parser_ParserState_next(x_4, x_7, x_5);
lean_dec(x_5);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_18 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_17, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_satisfyFn(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 2);
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
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_takeUntilFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_takeWhileFn___lambda__1(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_box_uint32(x_2);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
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
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Parser_takeUntilFn(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_Lean_Parser_takeWhileFn___lambda__1(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_takeWhileFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhile1Fn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_1);
x_5 = l_Lean_Parser_satisfyFn(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhile1Fn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_takeWhile1Fn(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_finishCommentBlock_eoi___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unterminated comment");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock_eoi(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_Lean_Parser_finishCommentBlock_eoi___closed__1;
x_4 = l_Lean_Parser_ParserState_mkUnexpectedError(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_3, 2);
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
lean_object* x_25; 
lean_dec(x_9);
lean_dec(x_1);
x_25 = l_Lean_Parser_finishCommentBlock_eoi(x_3);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = lean_string_utf8_at_end(x_5, x_9);
if (x_26 == 0)
{
uint32_t x_27; uint32_t x_28; uint8_t x_29; 
x_27 = lean_string_utf8_get(x_5, x_9);
x_28 = 47;
x_29 = x_27 == x_28;
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = l_Lean_Parser_ParserState_next(x_3, x_5, x_9);
lean_dec(x_9);
x_3 = x_30;
goto _start;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_dec_eq(x_1, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_nat_sub(x_1, x_32);
lean_dec(x_1);
x_35 = l_Lean_Parser_ParserState_next(x_3, x_5, x_9);
lean_dec(x_9);
x_1 = x_34;
x_3 = x_35;
goto _start;
}
else
{
lean_object* x_37; 
lean_dec(x_1);
x_37 = l_Lean_Parser_ParserState_next(x_3, x_5, x_9);
lean_dec(x_9);
return x_37;
}
}
}
else
{
lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_1);
x_38 = l_Lean_Parser_finishCommentBlock_eoi(x_3);
return x_38;
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_6);
lean_dec(x_1);
x_39 = l_Lean_Parser_finishCommentBlock_eoi(x_3);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_finishCommentBlock(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_whitespace___lambda__1(uint32_t x_1) {
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
static lean_object* _init_l_Lean_Parser_whitespace___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tabs are not allowed; please configure your editor to expand them");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_string_utf8_at_end(x_4, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_7 = lean_string_utf8_get(x_4, x_5);
x_8 = 9;
x_9 = x_7 == x_8;
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Char_isWhitespace(x_7);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 45;
x_12 = x_7 == x_11;
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 47;
x_14 = x_7 == x_13;
if (x_14 == 0)
{
lean_dec(x_5);
return x_2;
}
else
{
lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_15 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
x_16 = lean_string_utf8_get(x_4, x_15);
x_17 = x_16 == x_11;
if (x_17 == 0)
{
lean_dec(x_15);
return x_2;
}
else
{
lean_object* x_18; uint32_t x_19; uint8_t x_20; 
x_18 = lean_string_utf8_next(x_4, x_15);
lean_dec(x_15);
x_19 = lean_string_utf8_get(x_4, x_18);
x_20 = x_19 == x_11;
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; 
x_21 = 33;
x_22 = x_19 == x_21;
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = l_Lean_Parser_ParserState_next(x_2, x_4, x_18);
lean_dec(x_18);
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Lean_Parser_finishCommentBlock(x_24, x_1, x_23);
x_26 = lean_ctor_get(x_25, 4);
lean_inc(x_26);
x_27 = lean_box(0);
x_28 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
return x_25;
}
else
{
x_2 = x_25;
goto _start;
}
}
else
{
lean_dec(x_18);
return x_2;
}
}
else
{
lean_dec(x_18);
return x_2;
}
}
}
}
else
{
lean_object* x_30; uint32_t x_31; uint8_t x_32; 
x_30 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
x_31 = lean_string_utf8_get(x_4, x_30);
x_32 = x_31 == x_11;
if (x_32 == 0)
{
lean_dec(x_30);
return x_2;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = l_Lean_Parser_ParserState_next(x_2, x_4, x_30);
lean_dec(x_30);
x_34 = l_Lean_Parser_whitespace___closed__1;
x_35 = l_Lean_Parser_takeUntilFn(x_34, x_1, x_33);
x_36 = lean_ctor_get(x_35, 4);
lean_inc(x_36);
x_37 = lean_box(0);
x_38 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_36, x_37);
lean_dec(x_36);
if (x_38 == 0)
{
return x_35;
}
else
{
x_2 = x_35;
goto _start;
}
}
}
}
else
{
lean_object* x_40; 
x_40 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_5);
x_2 = x_40;
goto _start;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_5);
x_42 = lean_box(0);
x_43 = l_Lean_Parser_whitespace___closed__2;
x_44 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_43, x_42);
return x_44;
}
}
else
{
lean_dec(x_5);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace___lambda__1___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_whitespace(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkEmptySubstringAt(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_4, 2);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_7);
lean_inc(x_6);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_7);
x_11 = lean_string_utf8_byte_size(x_9);
x_12 = lean_nat_add(x_1, x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_13, 2, x_10);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
x_15 = l_Lean_Parser_ParserState_pushSyntax(x_4, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = l_Lean_Parser_whitespace(x_3, x_4);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_inc(x_6);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_7);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_string_utf8_byte_size(x_9);
x_20 = lean_nat_add(x_1, x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_1);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_20);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_9);
x_23 = l_Lean_Parser_ParserState_pushSyntax(x_16, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_inc(x_3);
x_6 = lean_apply_2(x_1, x_3, x_4);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Parser_rawFn(x_1, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_chFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn(uint32_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_5 = lean_box_uint32(x_1);
x_6 = lean_alloc_closure((void*)(l_UInt32_decEq___boxed), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_8 = lean_string_push(x_7, x_1);
x_9 = l_Lean_Parser_chFn___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_string_append(x_10, x_9);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
x_13 = l_Lean_Parser_satisfyFn(x_6, x_11, x_3, x_4);
x_14 = lean_ctor_get(x_13, 4);
lean_inc(x_14);
x_15 = lean_box(0);
x_16 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_14, x_15);
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
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___elambda__1(uint32_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_5 = lean_box_uint32(x_1);
x_6 = lean_alloc_closure((void*)(l_UInt32_decEq___boxed), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_8 = lean_string_push(x_7, x_1);
x_9 = l_Lean_Parser_chFn___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_string_append(x_10, x_9);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
x_13 = l_Lean_Parser_satisfyFn(x_6, x_11, x_3, x_4);
x_14 = lean_ctor_get(x_13, 4);
lean_inc(x_14);
x_15 = lean_box(0);
x_16 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_14, x_15);
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
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh(uint32_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_box_uint32(x_1);
x_4 = lean_box(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_rawCh___elambda__1___boxed), 4, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
x_6 = l_Lean_Parser_errorAtSavedPos___closed__2;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_string_utf8_at_end(x_4, x_5);
if (x_6 == 0)
{
uint32_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_22; 
x_7 = lean_string_utf8_get(x_4, x_5);
x_8 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
x_22 = l_Char_isDigit(x_7);
if (x_22 == 0)
{
uint32_t x_23; uint8_t x_24; 
x_23 = 97;
x_24 = x_23 <= x_7;
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_box(0);
x_9 = x_25;
goto block_21;
}
else
{
uint32_t x_26; uint8_t x_27; 
x_26 = 102;
x_27 = x_7 <= x_26;
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_box(0);
x_9 = x_28;
goto block_21;
}
else
{
lean_object* x_29; 
x_29 = l_Lean_Parser_ParserState_setPos(x_2, x_8);
return x_29;
}
}
}
else
{
lean_object* x_30; 
x_30 = l_Lean_Parser_ParserState_setPos(x_2, x_8);
return x_30;
}
block_21:
{
uint32_t x_10; uint8_t x_11; 
lean_dec(x_9);
x_10 = 65;
x_11 = x_10 <= x_7;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = l_Lean_Parser_hexDigitFn___closed__1;
x_14 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_13, x_12);
return x_14;
}
else
{
uint32_t x_15; uint8_t x_16; 
x_15 = 70;
x_16 = x_7 <= x_15;
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
x_17 = lean_box(0);
x_18 = l_Lean_Parser_hexDigitFn___closed__1;
x_19 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_18, x_17);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = l_Lean_Parser_ParserState_setPos(x_2, x_8);
return x_20;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
x_31 = lean_box(0);
x_32 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_33 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_32, x_31);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_3, 2);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = l_Lean_Parser_quotedCharCoreFn___closed__1;
x_18 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_17, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = l_Lean_Parser_ParserState_next(x_3, x_5, x_6);
lean_dec(x_6);
x_20 = l_Lean_Parser_hexDigitFn(x_2, x_19);
x_21 = lean_ctor_get(x_20, 4);
lean_inc(x_21);
x_22 = lean_box(0);
x_23 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l_Lean_Parser_hexDigitFn(x_2, x_20);
x_25 = lean_ctor_get(x_24, 4);
lean_inc(x_25);
x_26 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_25, x_22);
lean_dec(x_25);
if (x_26 == 0)
{
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = l_Lean_Parser_hexDigitFn(x_2, x_24);
x_28 = lean_ctor_get(x_27, 4);
lean_inc(x_28);
x_29 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_28, x_22);
lean_dec(x_28);
if (x_29 == 0)
{
return x_27;
}
else
{
lean_object* x_30; 
x_30 = l_Lean_Parser_hexDigitFn(x_2, x_27);
return x_30;
}
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = l_Lean_Parser_ParserState_next(x_3, x_5, x_6);
lean_dec(x_6);
x_32 = l_Lean_Parser_hexDigitFn(x_2, x_31);
x_33 = lean_ctor_get(x_32, 4);
lean_inc(x_33);
x_34 = lean_box(0);
x_35 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
return x_32;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_Parser_hexDigitFn(x_2, x_32);
return x_36;
}
}
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Parser_ParserState_next(x_3, x_5, x_6);
lean_dec(x_6);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_6);
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_40 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_39, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_quotedCharCoreFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharDefault___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_quotedCharFn___closed__1;
x_4 = l_Lean_Parser_quotedCharCoreFn(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_quotedCharFn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
lean_inc_n(x_2, 2);
lean_inc(x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_2);
x_9 = lean_string_utf8_extract(x_6, x_2, x_7);
x_10 = l_Lean_Parser_whitespace(x_3, x_4);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_inc(x_7);
lean_inc(x_6);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_7);
x_14 = l_Lean_Syntax_mkLit(x_1, x_9, x_13);
x_15 = l_Lean_Parser_ParserState_pushSyntax(x_10, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_3, 2);
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
x_14 = lean_ctor_get(x_3, 4);
lean_inc(x_14);
lean_dec(x_3);
x_15 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_14, x_13);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = l_Lean_Parser_charLitFnAux___closed__1;
x_23 = l_Lean_Parser_ParserState_mkUnexpectedError(x_18, x_22, x_21);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_charLitKind;
x_25 = l_Lean_Parser_mkNodeToken(x_24, x_1, x_2, x_18);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_3);
x_26 = l_Lean_Parser_quotedCharFn___closed__1;
x_27 = l_Lean_Parser_quotedCharCoreFn(x_26, x_2, x_10);
x_28 = lean_ctor_get(x_27, 4);
lean_inc(x_28);
x_29 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_28, x_13);
lean_dec(x_28);
if (x_29 == 0)
{
lean_dec(x_1);
return x_27;
}
else
{
lean_object* x_30; uint32_t x_31; lean_object* x_32; lean_object* x_33; uint32_t x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_27, 2);
lean_inc(x_30);
x_31 = lean_string_utf8_get(x_5, x_30);
x_32 = lean_string_utf8_next(x_5, x_30);
lean_dec(x_30);
x_33 = l_Lean_Parser_ParserState_setPos(x_27, x_32);
x_34 = 39;
x_35 = x_31 == x_34;
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_36 = lean_box(0);
x_37 = l_Lean_Parser_charLitFnAux___closed__1;
x_38 = l_Lean_Parser_ParserState_mkUnexpectedError(x_33, x_37, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_charLitKind;
x_40 = l_Lean_Parser_mkNodeToken(x_39, x_1, x_2, x_33);
return x_40;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_6);
lean_dec(x_1);
x_41 = lean_box(0);
x_42 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_43 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_42, x_41);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_charLitFnAux(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_strLitFnAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unterminated string literal");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_3, 2);
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
x_18 = lean_ctor_get(x_17, 4);
lean_inc(x_18);
x_19 = lean_box(0);
x_20 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_18, x_19);
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
x_24 = l_Lean_Parser_strLitFnAux___closed__1;
x_25 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_3, x_24, x_1);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptDot(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 2);
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
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptDot___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_decimalNumberFn_parseOptDot(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint32_t x_24; uint32_t x_25; uint8_t x_26; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 2);
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
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_decimalNumberFn_parseOptExp(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_4 = l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1;
x_5 = l_Lean_Parser_takeWhileFn(x_4, x_2, x_3);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_5, 2);
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
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_decimalNumberFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_binNumberFn___lambda__1(uint32_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l_Lean_Parser_binNumberFn___closed__1;
x_5 = l_Lean_Parser_binNumberFn___closed__2;
x_6 = l_Lean_Parser_satisfyFn(x_4, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___lambda__1___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_binNumberFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_octalNumberFn___lambda__1(uint32_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l_Lean_Parser_octalNumberFn___closed__1;
x_5 = l_Lean_Parser_octalNumberFn___closed__2;
x_6 = l_Lean_Parser_satisfyFn(x_4, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___lambda__1___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_octalNumberFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_hexNumberFn___lambda__1(uint32_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l_Lean_Parser_hexNumberFn___closed__1;
x_5 = l_Lean_Parser_hexNumberFn___closed__2;
x_6 = l_Lean_Parser_satisfyFn(x_4, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___lambda__1___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 2);
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
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_5);
x_43 = lean_box(0);
x_44 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_45 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_44, x_43);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_numberFnAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isIdCont(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; uint32_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 2);
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
LEAN_EXPORT lean_object* l_Lean_Parser_isIdCont___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_mkTokenAndFixPos___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = l_Lean_Parser_mkTokenAndFixPos___closed__1;
x_7 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_6, x_1, x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_3, 6);
lean_inc(x_9);
x_11 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_mkTokenAndFixPos___spec__1(x_10, x_2);
lean_dec(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc_n(x_1, 2);
lean_inc(x_13);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 2, x_1);
x_15 = lean_string_utf8_byte_size(x_9);
x_16 = lean_nat_add(x_1, x_15);
lean_dec(x_15);
lean_inc(x_16);
x_17 = l_Lean_Parser_ParserState_setPos(x_4, x_16);
x_18 = l_Lean_Parser_whitespace(x_3, x_17);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
lean_inc(x_16);
lean_inc(x_13);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_1);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_21, 3, x_16);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_9);
x_23 = l_Lean_Parser_ParserState_pushSyntax(x_18, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
x_24 = lean_box(0);
x_25 = l_Lean_Parser_mkTokenAndFixPos___closed__2;
x_26 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_25, x_1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_ctor_get(x_3, 6);
lean_inc(x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_27);
x_30 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_mkTokenAndFixPos___spec__1(x_28, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_31 = lean_ctor_get(x_3, 0);
x_32 = lean_ctor_get(x_31, 0);
lean_inc_n(x_1, 2);
lean_inc(x_32);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_1);
lean_ctor_set(x_33, 2, x_1);
x_34 = lean_string_utf8_byte_size(x_27);
x_35 = lean_nat_add(x_1, x_34);
lean_dec(x_34);
lean_inc(x_35);
x_36 = l_Lean_Parser_ParserState_setPos(x_4, x_35);
x_37 = l_Lean_Parser_whitespace(x_3, x_36);
x_38 = lean_ctor_get(x_37, 2);
lean_inc(x_38);
lean_inc(x_35);
lean_inc(x_32);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_1);
lean_ctor_set(x_40, 2, x_39);
lean_ctor_set(x_40, 3, x_35);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_27);
x_42 = l_Lean_Parser_ParserState_pushSyntax(x_37, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_27);
x_43 = lean_box(0);
x_44 = l_Lean_Parser_mkTokenAndFixPos___closed__2;
x_45 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_44, x_1, x_43);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_mkTokenAndFixPos___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_mkTokenAndFixPos___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_mkTokenAndFixPos(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
x_7 = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(x_1, x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
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
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_inc_n(x_1, 2);
lean_inc(x_9);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_13, 2, x_1);
lean_inc(x_6);
lean_inc(x_9);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_12);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_1);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_6);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_3);
lean_ctor_set(x_17, 3, x_16);
x_18 = l_Lean_Parser_ParserState_pushSyntax(x_11, x_17);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_3);
x_19 = l_Lean_Parser_mkTokenAndFixPos(x_1, x_2, x_4, x_5);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_mkIdResult(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux_parse___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = l_Lean_Parser_ParserState_next(x_1, x_2, x_9);
x_11 = lean_string_utf8_extract(x_2, x_3, x_9);
lean_dec(x_3);
x_12 = lean_name_mk_string(x_4, x_11);
x_13 = l_Lean_Parser_isIdCont(x_2, x_10);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_2);
x_14 = l_Lean_Parser_mkIdResult(x_5, x_6, x_12, x_7, x_10);
lean_dec(x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_string_utf8_next(x_2, x_9);
lean_dec(x_9);
x_16 = l_Lean_Parser_ParserState_next(x_10, x_2, x_15);
lean_dec(x_15);
lean_dec(x_2);
x_17 = l_Lean_Parser_identFnAux_parse(x_5, x_6, x_12, x_7, x_16);
return x_17;
}
}
}
static lean_object* _init_l_Lean_Parser_identFnAux_parse___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_isIdRest___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_identFnAux_parse___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_isIdEndEscape___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_identFnAux_parse___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unterminated identifier escape");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux_parse___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint32_t x_9; uint32_t x_10; uint8_t x_11; 
lean_dec(x_8);
x_9 = lean_string_utf8_get(x_1, x_2);
x_10 = l_Lean_idBeginEscape;
x_11 = x_9 == x_10;
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_isIdFirst(x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Parser_mkTokenAndFixPos(x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = l_Lean_Parser_ParserState_next(x_6, x_1, x_2);
x_15 = l_Lean_Parser_identFnAux_parse___lambda__2___closed__1;
x_16 = l_Lean_Parser_takeWhileFn(x_15, x_5, x_14);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
x_18 = lean_string_utf8_extract(x_1, x_2, x_17);
lean_dec(x_2);
x_19 = lean_name_mk_string(x_7, x_18);
x_20 = l_Lean_Parser_isIdCont(x_1, x_16);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_1);
x_21 = l_Lean_Parser_mkIdResult(x_3, x_4, x_19, x_5, x_16);
lean_dec(x_5);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Parser_ParserState_next(x_16, x_1, x_17);
lean_dec(x_17);
lean_dec(x_1);
x_23 = l_Lean_Parser_identFnAux_parse(x_3, x_4, x_19, x_5, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
lean_inc(x_24);
x_25 = l_Lean_Parser_ParserState_setPos(x_6, x_24);
x_26 = l_Lean_Parser_identFnAux_parse___lambda__2___closed__2;
x_27 = l_Lean_Parser_takeUntilFn(x_26, x_5, x_25);
x_28 = lean_ctor_get(x_27, 2);
lean_inc(x_28);
x_29 = lean_string_utf8_at_end(x_1, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
x_31 = l_Lean_Parser_identFnAux_parse___lambda__1(x_27, x_1, x_24, x_7, x_3, x_4, x_5, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = l_Lean_Parser_identFnAux_parse___lambda__2___closed__3;
x_33 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_27, x_32, x_24);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_string_utf8_at_end(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Parser_identFnAux_parse___lambda__2(x_7, x_8, x_1, x_2, x_4, x_5, x_3, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_14 = l_Lean_Parser_ParserState_mkUnexpectedError(x_5, x_13, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux_parse___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_identFnAux_parse___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_identFnAux_parse(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(uint32_t x_1) {
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape___boxed(lean_object* x_1) {
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
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid Name literal");
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Parser_ParserState_next(x_3, x_5, x_1);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_Lean_Parser_identFnAux_parse(x_1, x_6, x_8, x_2, x_7);
x_10 = lean_ctor_get(x_9, 4);
lean_inc(x_10);
x_11 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_10, x_6);
lean_dec(x_10);
if (x_11 == 0)
{
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 3)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Parser_ParserState_popSyntax(x_9);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_string_utf8_extract(x_17, x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_21 = l_Lean_nameLitKind;
x_22 = l_Lean_Syntax_mkLit(x_21, x_20, x_14);
x_23 = l_Lean_Parser_ParserState_pushSyntax(x_16, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
x_24 = l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__1;
x_25 = l_Lean_Parser_ParserState_mkError(x_9, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 2);
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
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_4);
x_26 = l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(x_5, x_1, x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateCache(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_array_get_size(x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_2, 4);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_2, 0);
lean_dec(x_15);
x_16 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_4);
lean_inc(x_6);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_box(0);
lean_ctor_set(x_2, 4, x_18);
lean_ctor_set(x_2, 3, x_17);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_19 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_4);
lean_inc(x_6);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_6);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_5);
lean_ctor_set(x_22, 2, x_6);
lean_ctor_set(x_22, 3, x_20);
lean_ctor_set(x_22, 4, x_21);
return x_22;
}
}
else
{
lean_dec(x_6);
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
LEAN_EXPORT lean_object* l_Lean_Parser_tokenFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_string_utf8_at_end(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_nat_dec_eq(x_9, x_6);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
x_11 = l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(x_2, x_3);
x_12 = l___private_Lean_Parser_Basic_0__Lean_Parser_updateCache(x_6, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_2);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
x_14 = l_Lean_Parser_ParserState_pushSyntax(x_3, x_13);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = l_Lean_Parser_ParserState_setPos(x_14, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_2);
x_17 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_18 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_17, x_1);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekTokenAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l_Lean_Parser_tokenFn(x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_9);
lean_dec(x_9);
x_11 = l_Lean_Parser_ParserState_restore(x_7, x_4, x_5);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_inc(x_7);
x_14 = l_Lean_Parser_ParserState_restore(x_7, x_4, x_5);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekToken(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
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
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_string_utf8_at_end(x_4, x_5);
lean_dec(x_4);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = l_Lean_Parser_ParserState_mkEOIError___closed__1;
x_12 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_11, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
lean_inc(x_2);
x_8 = l_Lean_Parser_tokenFn(x_2, x_3, x_4);
x_9 = lean_ctor_get(x_8, 4);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 2)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_1(x_1, x_14);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_6);
x_18 = l_Lean_Parser_ParserState_mkErrorsAt(x_8, x_2, x_7, x_17);
return x_18;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_8;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_6);
x_20 = l_Lean_Parser_ParserState_mkErrorsAt(x_8, x_2, x_7, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
lean_inc(x_6);
x_10 = l_Lean_Parser_tokenFn(x_6, x_3, x_4);
x_11 = lean_ctor_get(x_10, 4);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
x_15 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 2)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_string_dec_eq(x_16, x_1);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_8);
x_19 = l_Lean_Parser_ParserState_mkErrorsAt(x_10, x_6, x_9, x_18);
return x_19;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
return x_10;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_15);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_8);
x_21 = l_Lean_Parser_ParserState_mkErrorsAt(x_10, x_6, x_9, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_symbolFnAux(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___elambda__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_symbolInfo___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Parser_chFn___closed__1;
x_5 = lean_string_append(x_4, x_1);
x_6 = lean_string_append(x_5, x_4);
x_7 = l_Lean_Parser_symbolFnAux(x_1, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_symbolFn(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_symbolNoAntiquot(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailNoWs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailNoWs___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_checkTailNoWs(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_box(0);
lean_inc(x_2);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Parser_tokenFn(x_9, x_3, x_4);
x_11 = lean_ctor_get(x_10, 4);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
x_15 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_14);
lean_dec(x_14);
switch (lean_obj_tag(x_15)) {
case 2:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_string_dec_eq(x_1, x_16);
lean_dec(x_16);
lean_dec(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_6);
x_19 = l_Lean_Parser_ParserState_mkErrorAt(x_10, x_2, x_7, x_18);
return x_19;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
case 3:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 2);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_string_utf8_extract(x_22, x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_26 = lean_string_dec_eq(x_1, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_1);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_6);
x_28 = l_Lean_Parser_ParserState_mkErrorAt(x_10, x_2, x_7, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_29 = l_Lean_Parser_ParserState_popSyntax(x_10);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_1);
x_31 = l_Lean_Parser_ParserState_pushSyntax(x_29, x_30);
return x_31;
}
}
default: 
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_15);
lean_dec(x_1);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_6);
x_33 = l_Lean_Parser_ParserState_mkErrorAt(x_10, x_2, x_7, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Parser_chFn___closed__1;
x_5 = lean_string_append(x_4, x_1);
x_6 = lean_string_append(x_5, x_4);
x_7 = l_Lean_Parser_nonReservedSymbolFnAux(x_1, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__2(lean_object* x_1) {
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
lean_object* x_1; 
x_1 = lean_mk_string("ident");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_nonReservedSymbolInfo___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_nonReservedSymbolInfo___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object* x_1, uint8_t x_2) {
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
x_9 = l_Lean_Parser_nonReservedSymbolInfo___closed__4;
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
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_nonReservedSymbolInfo___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_nonReservedSymbolInfo___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Parser_nonReservedSymbolInfo(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot(lean_object* x_1, uint8_t x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Parser_nonReservedSymbolNoAntiquot(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 2);
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
LEAN_EXPORT lean_object* l_Lean_Parser_strAux_parse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_strAux_parse(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_strAux_parse(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_strAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailWs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailWs___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_checkTailWs(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkWsBeforeFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkWsBeforeFn(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkWsBefore___elambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailLinebreak(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint32_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_dec(x_2);
x_4 = 10;
x_5 = l_Substring_contains(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailLinebreak___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_checkTailLinebreak(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_4);
lean_dec(x_4);
x_6 = l_Lean_Parser_checkTailLinebreak(x_5);
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
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkLinebreakBeforeFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkLinebreakBeforeFn(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkLinebreakBefore___elambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_epsilonInfo;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkLinebreakBefore___elambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findSomeRevM_x3f_find___at___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkNoWsBeforeFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkNoWsBeforeFn(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkNoWsBefore___elambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
lean_inc(x_3);
x_9 = l_Lean_Parser_tokenFn(x_3, x_4, x_5);
x_10 = lean_ctor_get(x_9, 4);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
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
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = lean_string_dec_eq(x_15, x_2);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_7);
x_19 = l_Lean_Parser_ParserState_mkErrorsAt(x_9, x_3, x_8, x_18);
return x_19;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_9;
}
}
else
{
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_9;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_7);
x_21 = l_Lean_Parser_ParserState_mkErrorsAt(x_9, x_3, x_8, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_unicodeSymbolFnAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__1___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l_Lean_Parser_chFn___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_unicodeSymbolFn(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_unicodeSymbolNoAntiquot(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo___elambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo___elambda__2(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_mkAtomicInfo___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_mkAtomicInfo___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_numLitFn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_numberFnAux___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_Parser_numLitFn___closed__1;
x_7 = l_Lean_Parser_tokenFn(x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_11);
lean_dec(x_11);
x_13 = l_Lean_numLitKind;
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_4);
x_16 = l_Lean_Parser_numberFnAux___closed__1;
x_17 = l_Lean_Parser_ParserState_mkErrorAt(x_7, x_16, x_5, x_15);
return x_17;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("numLit");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_numLitNoAntiquot___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_numLitFn), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_numLitNoAntiquot___closed__2;
x_2 = l_Lean_Parser_numLitNoAntiquot___closed__3;
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
x_1 = l_Lean_Parser_numLitNoAntiquot___closed__4;
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
static lean_object* _init_l_Lean_Parser_scientificLitFn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_scientificLitFn___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_Parser_scientificLitFn___closed__2;
x_7 = l_Lean_Parser_tokenFn(x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_11);
lean_dec(x_11);
x_13 = l_Lean_scientificLitKind;
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_4);
x_16 = l_Lean_Parser_scientificLitFn___closed__1;
x_17 = l_Lean_Parser_ParserState_mkErrorAt(x_7, x_16, x_5, x_15);
return x_17;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("scientificLit");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_scientificLitNoAntiquot___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_scientificLitFn), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_scientificLitNoAntiquot___closed__2;
x_2 = l_Lean_Parser_scientificLitNoAntiquot___closed__3;
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
x_1 = l_Lean_Parser_scientificLitNoAntiquot___closed__4;
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
static lean_object* _init_l_Lean_Parser_strLitFn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_strLitFn___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_Parser_strLitFn___closed__2;
x_7 = l_Lean_Parser_tokenFn(x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_11);
lean_dec(x_11);
x_13 = l_Lean_strLitKind;
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_4);
x_16 = l_Lean_Parser_strLitFn___closed__1;
x_17 = l_Lean_Parser_ParserState_mkErrorAt(x_7, x_16, x_5, x_15);
return x_17;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("strLit");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_strLitNoAntiquot___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_strLitFn), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_strLitNoAntiquot___closed__2;
x_2 = l_Lean_Parser_strLitNoAntiquot___closed__3;
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
x_1 = l_Lean_Parser_strLitNoAntiquot___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_charLitFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("char literal");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_charLitFn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_charLitFn___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_charLitFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("character literal");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_Parser_charLitFn___closed__2;
x_7 = l_Lean_Parser_tokenFn(x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_11);
lean_dec(x_11);
x_13 = l_Lean_charLitKind;
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_4);
x_16 = l_Lean_Parser_charLitFn___closed__3;
x_17 = l_Lean_Parser_ParserState_mkErrorAt(x_7, x_16, x_5, x_15);
return x_17;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("charLit");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_charLitNoAntiquot___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_charLitFn), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_charLitNoAntiquot___closed__2;
x_2 = l_Lean_Parser_charLitNoAntiquot___closed__3;
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
x_1 = l_Lean_Parser_charLitNoAntiquot___closed__4;
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
static lean_object* _init_l_Lean_Parser_nameLitFn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_nameLitFn___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_Parser_nameLitFn___closed__2;
x_7 = l_Lean_Parser_tokenFn(x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_11);
lean_dec(x_11);
x_13 = l_Lean_nameLitKind;
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_4);
x_16 = l_Lean_Parser_nameLitFn___closed__1;
x_17 = l_Lean_Parser_ParserState_mkErrorAt(x_7, x_16, x_5, x_15);
return x_17;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nameLit");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_nameLitNoAntiquot___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_nameLitFn), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_nameLitNoAntiquot___closed__2;
x_2 = l_Lean_Parser_nameLitNoAntiquot___closed__3;
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
x_1 = l_Lean_Parser_nameLitNoAntiquot___closed__4;
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
static lean_object* _init_l_Lean_Parser_identFn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_identFn___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_Parser_identFn___closed__2;
x_7 = l_Lean_Parser_tokenFn(x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_11);
lean_dec(x_11);
x_13 = l_Lean_Syntax_isIdent(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_4);
x_15 = l_Lean_Parser_identFn___closed__1;
x_16 = l_Lean_Parser_ParserState_mkErrorAt(x_7, x_15, x_5, x_14);
return x_16;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
}
}
static lean_object* _init_l_Lean_Parser_identNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_nonReservedSymbolInfo___closed__3;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_rawIdentFn), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_rawIdentNoAntiquot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_errorAtSavedPos___closed__2;
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
static lean_object* _init_l_Lean_Parser_identEqFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected identifier '");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEqFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = l_Lean_Parser_identFn___closed__2;
x_8 = l_Lean_Parser_tokenFn(x_7, x_2, x_3);
x_9 = lean_ctor_get(x_8, 4);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 3)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_name_eq(x_14, x_1);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = 1;
x_17 = l_Lean_Name_toString(x_1, x_16);
x_18 = l_Lean_Parser_identEqFn___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lean_Parser_chFn___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_5);
x_23 = l_Lean_Parser_ParserState_mkErrorAt(x_8, x_21, x_6, x_22);
return x_23;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_1);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_5);
x_25 = l_Lean_Parser_identFn___closed__1;
x_26 = l_Lean_Parser_ParserState_mkErrorAt(x_8, x_25, x_6, x_24);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEq(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_1);
x_4 = l_Array_shrink___rarg(x_1, x_2);
x_5 = lean_array_push(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_keepTop(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_Parser_ParserState_keepTop(x_4, x_2);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_11 = l_Lean_Parser_ParserState_keepTop(x_6, x_2);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_keepNewError(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 4);
lean_dec(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_dec(x_8);
x_9 = l_Array_shrink___rarg(x_6, x_2);
lean_ctor_set(x_1, 4, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_13 = l_Array_shrink___rarg(x_10, x_2);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_12);
lean_ctor_set(x_14, 4, x_4);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_ParserState_keepPrevError(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = l___private_Lean_Parser_Basic_0__Lean_Parser_beqError____x40_Lean_Parser_Basic___hyg_353_(x_3, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 4);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_dec(x_17);
x_18 = l_Array_shrink___rarg(x_5, x_2);
x_19 = l_Lean_Parser_Error_merge(x_3, x_10);
lean_ctor_set(x_4, 0, x_19);
lean_ctor_set(x_1, 0, x_18);
return x_1;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_20 = l_Array_shrink___rarg(x_5, x_2);
x_21 = l_Lean_Parser_Error_merge(x_3, x_10);
lean_ctor_set(x_4, 0, x_21);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_6);
lean_ctor_set(x_22, 2, x_7);
lean_ctor_set(x_22, 3, x_8);
lean_ctor_set(x_22, 4, x_4);
return x_22;
}
}
else
{
lean_free_object(x_4);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_1;
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
lean_dec(x_4);
x_24 = l___private_Lean_Parser_Basic_0__Lean_Parser_beqError____x40_Lean_Parser_Basic___hyg_353_(x_3, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 x_25 = x_1;
} else {
 lean_dec_ref(x_1);
 x_25 = lean_box(0);
}
x_26 = l_Array_shrink___rarg(x_5, x_2);
x_27 = l_Lean_Parser_Error_merge(x_3, x_23);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
if (lean_is_scalar(x_25)) {
 x_29 = lean_alloc_ctor(0, 5, 0);
} else {
 x_29 = x_25;
}
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_6);
lean_ctor_set(x_29, 2, x_7);
lean_ctor_set(x_29, 3, x_8);
lean_ctor_set(x_29, 4, x_28);
return x_29;
}
else
{
lean_dec(x_23);
lean_dec(x_8);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_ParserState_mergeErrors(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 4);
lean_dec(x_5);
x_6 = l_Lean_Parser_ParserState_keepTop(x_4, x_2);
x_7 = lean_box(0);
lean_ctor_set(x_1, 4, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_12 = l_Lean_Parser_ParserState_keepTop(x_8, x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_11);
lean_ctor_set(x_14, 4, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_keepLatest(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_ParserState_keepLatest(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_invalidLongestMatchParser(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_invalidLongestMatchParser___closed__1;
x_3 = l_Lean_Parser_ParserState_mkError(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_apply_2(x_1, x_2, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
x_11 = lean_nat_dec_eq(x_8, x_10);
lean_dec(x_10);
lean_dec(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_6, 4);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Parser_ParserState_shrinkStack(x_6, x_3);
x_16 = lean_box(0);
x_17 = l_Lean_Parser_ParserState_pushSyntax(x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Parser_invalidLongestMatchParser___closed__1;
x_19 = l_Lean_Parser_ParserState_mkError(x_6, x_18);
return x_19;
}
}
else
{
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_dec(x_8);
x_9 = lean_array_get_size(x_7);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_10 = l_Lean_Parser_maxPrec;
lean_ctor_set(x_5, 1, x_10);
x_11 = lean_box(0);
x_12 = l_Lean_Parser_runLongestMatchParser___lambda__1(x_3, x_4, x_9, x_5, x_11);
lean_dec(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
lean_ctor_set(x_5, 1, x_2);
x_14 = l_Lean_Parser_ParserState_pushSyntax(x_5, x_13);
x_15 = lean_box(0);
x_16 = l_Lean_Parser_runLongestMatchParser___lambda__1(x_3, x_4, x_9, x_14, x_15);
lean_dec(x_9);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 2);
x_19 = lean_ctor_get(x_5, 3);
x_20 = lean_ctor_get(x_5, 4);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_21 = lean_array_get_size(x_17);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_22 = l_Lean_Parser_maxPrec;
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_20);
x_24 = lean_box(0);
x_25 = l_Lean_Parser_runLongestMatchParser___lambda__1(x_3, x_4, x_21, x_23, x_24);
lean_dec(x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set(x_27, 2, x_18);
lean_ctor_set(x_27, 3, x_19);
lean_ctor_set(x_27, 4, x_20);
x_28 = l_Lean_Parser_ParserState_pushSyntax(x_27, x_26);
x_29 = lean_box(0);
x_30 = l_Lean_Parser_runLongestMatchParser___lambda__1(x_3, x_4, x_21, x_28, x_29);
lean_dec(x_21);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_runLongestMatchParser___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 4);
lean_inc(x_13);
x_14 = lean_array_get_size(x_10);
lean_dec(x_10);
x_15 = l_Lean_Parser_ParserState_restore(x_9, x_14, x_4);
x_16 = l_Lean_Parser_runLongestMatchParser(x_1, x_3, x_7, x_8, x_15);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 4);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_73; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 3);
lean_inc(x_21);
x_73 = lean_nat_dec_lt(x_12, x_20);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = lean_nat_dec_eq(x_20, x_12);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_box(0);
x_22 = x_75;
goto block_72;
}
else
{
uint8_t x_76; 
x_76 = lean_nat_dec_lt(x_5, x_6);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_box(0);
x_22 = x_77;
goto block_72;
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
x_78 = l_Lean_Parser_ParserState_keepLatest(x_16, x_2);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_6);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
x_80 = l_Lean_Parser_ParserState_keepLatest(x_16, x_2);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_6);
return x_81;
}
block_72:
{
uint8_t x_23; 
lean_dec(x_22);
x_23 = lean_nat_dec_lt(x_20, x_12);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = lean_nat_dec_eq(x_20, x_12);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_16, 4);
lean_dec(x_26);
x_27 = lean_ctor_get(x_16, 3);
lean_dec(x_27);
x_28 = lean_ctor_get(x_16, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_16, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_16, 0);
lean_dec(x_30);
x_31 = l_Nat_min(x_19, x_11);
lean_dec(x_11);
lean_dec(x_19);
lean_ctor_set(x_16, 1, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_6);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_16);
x_33 = l_Nat_min(x_19, x_11);
lean_dec(x_11);
lean_dec(x_19);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_18);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_20);
lean_ctor_set(x_34, 3, x_21);
lean_ctor_set(x_34, 4, x_17);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_6);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_lt(x_6, x_5);
if (x_36 == 0)
{
uint8_t x_37; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_5);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_16, 4);
lean_dec(x_38);
x_39 = lean_ctor_get(x_16, 3);
lean_dec(x_39);
x_40 = lean_ctor_get(x_16, 2);
lean_dec(x_40);
x_41 = lean_ctor_get(x_16, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_16, 0);
lean_dec(x_42);
x_43 = l_Nat_min(x_19, x_11);
lean_dec(x_11);
lean_dec(x_19);
lean_ctor_set(x_16, 1, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_16);
lean_ctor_set(x_44, 1, x_6);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_16);
x_45 = l_Nat_min(x_19, x_11);
lean_dec(x_11);
lean_dec(x_19);
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_18);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_20);
lean_ctor_set(x_46, 3, x_21);
lean_ctor_set(x_46, 4, x_17);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_6);
return x_47;
}
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_inc(x_12);
x_48 = l_Lean_Parser_ParserState_restore(x_16, x_14, x_12);
lean_dec(x_14);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_48, 4);
lean_dec(x_50);
x_51 = lean_ctor_get(x_48, 3);
lean_dec(x_51);
x_52 = lean_ctor_get(x_48, 2);
lean_dec(x_52);
x_53 = lean_ctor_get(x_48, 1);
lean_dec(x_53);
x_54 = lean_box(0);
lean_ctor_set(x_48, 4, x_54);
lean_ctor_set(x_48, 3, x_21);
lean_ctor_set(x_48, 2, x_12);
lean_ctor_set(x_48, 1, x_11);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_5);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
lean_dec(x_48);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_11);
lean_ctor_set(x_58, 2, x_12);
lean_ctor_set(x_58, 3, x_21);
lean_ctor_set(x_58, 4, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_5);
return x_59;
}
}
}
}
else
{
lean_object* x_60; uint8_t x_61; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_inc(x_12);
x_60 = l_Lean_Parser_ParserState_restore(x_16, x_14, x_12);
lean_dec(x_14);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_60, 4);
lean_dec(x_62);
x_63 = lean_ctor_get(x_60, 3);
lean_dec(x_63);
x_64 = lean_ctor_get(x_60, 2);
lean_dec(x_64);
x_65 = lean_ctor_get(x_60, 1);
lean_dec(x_65);
x_66 = lean_box(0);
lean_ctor_set(x_60, 4, x_66);
lean_ctor_set(x_60, 3, x_21);
lean_ctor_set(x_60, 2, x_12);
lean_ctor_set(x_60, 1, x_11);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_5);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_60, 0);
lean_inc(x_68);
lean_dec(x_60);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_11);
lean_ctor_set(x_70, 2, x_12);
lean_ctor_set(x_70, 3, x_21);
lean_ctor_set(x_70, 4, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_5);
return x_71;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_17);
lean_dec(x_6);
x_82 = lean_ctor_get(x_16, 3);
lean_inc(x_82);
lean_inc(x_12);
x_83 = l_Lean_Parser_ParserState_restore(x_16, x_14, x_12);
lean_dec(x_14);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_83, 4);
lean_dec(x_85);
x_86 = lean_ctor_get(x_83, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_83, 2);
lean_dec(x_87);
x_88 = lean_ctor_get(x_83, 1);
lean_dec(x_88);
x_89 = lean_box(0);
lean_ctor_set(x_83, 4, x_89);
lean_ctor_set(x_83, 3, x_82);
lean_ctor_set(x_83, 2, x_12);
lean_ctor_set(x_83, 1, x_11);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_83);
lean_ctor_set(x_90, 1, x_5);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_83, 0);
lean_inc(x_91);
lean_dec(x_83);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_11);
lean_ctor_set(x_93, 2, x_12);
lean_ctor_set(x_93, 3, x_82);
lean_ctor_set(x_93, 4, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_5);
return x_94;
}
}
}
else
{
lean_object* x_95; 
lean_dec(x_11);
x_95 = lean_ctor_get(x_16, 4);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_96 = lean_ctor_get(x_16, 0);
lean_inc(x_96);
x_97 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_96);
lean_dec(x_96);
x_98 = l_Lean_Parser_ParserState_shrinkStack(x_16, x_2);
x_99 = l_Lean_Parser_ParserState_pushSyntax(x_98, x_97);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_6);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_116; 
lean_dec(x_95);
x_101 = lean_ctor_get(x_16, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_13, 0);
lean_inc(x_102);
x_116 = lean_nat_dec_lt(x_12, x_101);
if (x_116 == 0)
{
uint8_t x_117; 
x_117 = lean_nat_dec_eq(x_101, x_12);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_box(0);
x_103 = x_118;
goto block_115;
}
else
{
uint8_t x_119; 
x_119 = lean_nat_dec_lt(x_5, x_6);
if (x_119 == 0)
{
lean_object* x_120; 
x_120 = lean_box(0);
x_103 = x_120;
goto block_115;
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_121 = l_Lean_Parser_ParserState_keepNewError(x_16, x_2);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_6);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_123 = l_Lean_Parser_ParserState_keepNewError(x_16, x_2);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_6);
return x_124;
}
block_115:
{
uint8_t x_104; 
lean_dec(x_103);
x_104 = lean_nat_dec_lt(x_101, x_12);
if (x_104 == 0)
{
uint8_t x_105; 
x_105 = lean_nat_dec_eq(x_101, x_12);
lean_dec(x_101);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_106 = l_Lean_Parser_ParserState_mergeErrors(x_16, x_14, x_102);
lean_dec(x_14);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_6);
return x_107;
}
else
{
uint8_t x_108; 
x_108 = lean_nat_dec_lt(x_6, x_5);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_109 = l_Lean_Parser_ParserState_mergeErrors(x_16, x_14, x_102);
lean_dec(x_14);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_6);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_102);
lean_dec(x_6);
x_111 = l_Lean_Parser_ParserState_keepPrevError(x_16, x_14, x_12, x_13);
lean_dec(x_14);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_5);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_6);
x_113 = l_Lean_Parser_ParserState_keepPrevError(x_16, x_14, x_12, x_13);
lean_dec(x_14);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_5);
return x_114;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Parser_longestMatchStep(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
x_4 = lean_box(0);
x_5 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_3, x_4);
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
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = l_Lean_Parser_longestMatchMkResult(x_2, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_15 = l_Lean_Parser_longestMatchStep(x_1, x_2, x_3, x_4, x_5, x_12, x_14, x_7, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_5 = x_17;
x_6 = x_11;
x_8 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_longestMatchFnAux_parse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
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
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Parser_runLongestMatchParser(x_1, x_9, x_11, x_3, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_array_get_size(x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_3);
lean_inc(x_16);
lean_inc(x_1);
x_20 = l_Lean_Parser_runLongestMatchParser(x_1, x_16, x_19, x_3, x_4);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l_Lean_Parser_longestMatchFnAux_parse(x_1, x_15, x_16, x_17, x_21, x_7, x_3, x_20);
return x_22;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Parser_anyOfFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 5);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_6, 2);
x_8 = l_Lean_FileMap_toPosition(x_7, x_5);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
x_10 = l_Lean_FileMap_toPosition(x_7, x_9);
lean_dec(x_9);
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
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGeFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkColGeFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkColGeFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_errorAtSavedPos___closed__2;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGtFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 5);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_6, 2);
x_8 = l_Lean_FileMap_toPosition(x_7, x_5);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
x_10 = l_Lean_FileMap_toPosition(x_7, x_9);
lean_dec(x_9);
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
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGtFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkColGtFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkColGtFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_errorAtSavedPos___closed__2;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEqFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 5);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_6, 2);
x_8 = l_Lean_FileMap_toPosition(x_7, x_5);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
x_10 = l_Lean_FileMap_toPosition(x_7, x_9);
lean_dec(x_9);
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
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEqFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkLineEqFn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkLineEqFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_errorAtSavedPos___closed__2;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 5);
lean_dec(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_2, 5, x_8);
x_9 = lean_apply_2(x_4, x_2, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
x_14 = lean_ctor_get(x_2, 4);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_16 = lean_ctor_get(x_2, 6);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_17 = lean_ctor_get(x_3, 2);
lean_inc(x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_19, 3, x_13);
lean_ctor_set(x_19, 4, x_14);
lean_ctor_set(x_19, 5, x_18);
lean_ctor_set(x_19, 6, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*7, x_15);
x_20 = lean_apply_2(x_4, x_19, x_3);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 5);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_2, 5, x_7);
x_8 = lean_apply_2(x_4, x_2, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
x_13 = lean_ctor_get(x_2, 4);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_15 = lean_ctor_get(x_2, 6);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_11);
lean_ctor_set(x_17, 3, x_12);
lean_ctor_set(x_17, 4, x_13);
lean_ctor_set(x_17, 5, x_16);
lean_ctor_set(x_17, 6, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*7, x_14);
x_18 = lean_apply_2(x_4, x_17, x_3);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 6);
lean_dec(x_7);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_3, 6, x_8);
x_9 = lean_apply_2(x_5, x_3, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 4);
x_15 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_16 = lean_ctor_get(x_3, 5);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_2);
x_18 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_12);
lean_ctor_set(x_18, 3, x_13);
lean_ctor_set(x_18, 4, x_14);
lean_ctor_set(x_18, 5, x_16);
lean_ctor_set(x_18, 6, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*7, x_15);
x_19 = lean_apply_2(x_5, x_18, x_4);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 6);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_2, 6, x_7);
x_8 = lean_apply_2(x_4, x_2, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
x_13 = lean_ctor_get(x_2, 4);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_15 = lean_ctor_get(x_2, 5);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_11);
lean_ctor_set(x_17, 3, x_12);
lean_ctor_set(x_17, 4, x_13);
lean_ctor_set(x_17, 5, x_15);
lean_ctor_set(x_17, 6, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*7, x_14);
x_18 = lean_apply_2(x_4, x_17, x_3);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 2);
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
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn___boxed(lean_object* x_1, lean_object* x_2) {
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
x_1 = l_Lean_Parser_errorAtSavedPos___closed__2;
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
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_13 = l_Lean_Name_quickCmp(x_2, x_10);
switch (x_13) {
case 0:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_9, x_2, x_3);
x_15 = 0;
lean_ctor_set(x_1, 0, x_14);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
case 1:
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
default: 
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_12, x_2, x_3);
x_18 = 0;
lean_ctor_set(x_1, 3, x_17);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_18);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_23 = l_Lean_Name_quickCmp(x_2, x_20);
switch (x_23) {
case 0:
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_19, x_2, x_3);
x_25 = 0;
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_25);
return x_26;
}
case 1:
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
default: 
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_22, x_2, x_3);
x_30 = 0;
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 2);
x_36 = lean_ctor_get(x_1, 3);
x_37 = l_Lean_Name_quickCmp(x_2, x_34);
switch (x_37) {
case 0:
{
uint8_t x_38; 
x_38 = l_Std_RBNode_isRed___rarg(x_33);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_33, x_2, x_3);
x_40 = 1;
lean_ctor_set(x_1, 0, x_39);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_40);
return x_1;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_33, x_2, x_3);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 3);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_41, 3);
lean_dec(x_45);
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = 0;
lean_ctor_set(x_41, 0, x_43);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_47);
x_48 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_41, 1);
x_50 = lean_ctor_get(x_41, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = 0;
x_52 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 2, x_50);
lean_ctor_set(x_52, 3, x_43);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_51);
x_53 = 1;
lean_ctor_set(x_1, 0, x_52);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_53);
return x_1;
}
}
else
{
uint8_t x_54; 
x_54 = lean_ctor_get_uint8(x_43, sizeof(void*)*4);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_41);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_41, 1);
x_57 = lean_ctor_get(x_41, 2);
x_58 = lean_ctor_get(x_41, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_41, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_43);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_43, 0);
x_62 = lean_ctor_get(x_43, 1);
x_63 = lean_ctor_get(x_43, 2);
x_64 = lean_ctor_get(x_43, 3);
x_65 = 1;
lean_ctor_set(x_43, 3, x_61);
lean_ctor_set(x_43, 2, x_57);
lean_ctor_set(x_43, 1, x_56);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_65);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_64);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_65);
x_66 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_63);
lean_ctor_set(x_1, 1, x_62);
lean_ctor_set(x_1, 0, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; 
x_67 = lean_ctor_get(x_43, 0);
x_68 = lean_ctor_get(x_43, 1);
x_69 = lean_ctor_get(x_43, 2);
x_70 = lean_ctor_get(x_43, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_43);
x_71 = 1;
x_72 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_72, 0, x_42);
lean_ctor_set(x_72, 1, x_56);
lean_ctor_set(x_72, 2, x_57);
lean_ctor_set(x_72, 3, x_67);
lean_ctor_set_uint8(x_72, sizeof(void*)*4, x_71);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_70);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_71);
x_73 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_69);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_72);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_73);
return x_1;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_74 = lean_ctor_get(x_41, 1);
x_75 = lean_ctor_get(x_41, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_41);
x_76 = lean_ctor_get(x_43, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_43, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_43, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_43, 3);
lean_inc(x_79);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_80 = x_43;
} else {
 lean_dec_ref(x_43);
 x_80 = lean_box(0);
}
x_81 = 1;
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(1, 4, 1);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_42);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_75);
lean_ctor_set(x_82, 3, x_76);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_81);
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_34);
lean_ctor_set(x_83, 2, x_35);
lean_ctor_set(x_83, 3, x_36);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_81);
x_84 = 0;
lean_ctor_set(x_1, 3, x_83);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_82);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_84);
return x_1;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_41);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_41, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_41, 0);
lean_dec(x_87);
x_88 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_88);
x_89 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_89);
return x_1;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_41, 1);
x_91 = lean_ctor_get(x_41, 2);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_41);
x_92 = 0;
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_42);
lean_ctor_set(x_93, 1, x_90);
lean_ctor_set(x_93, 2, x_91);
lean_ctor_set(x_93, 3, x_43);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_92);
x_94 = 1;
lean_ctor_set(x_1, 0, x_93);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_94);
return x_1;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_42, sizeof(void*)*4);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_41);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_41, 1);
x_98 = lean_ctor_get(x_41, 2);
x_99 = lean_ctor_get(x_41, 3);
x_100 = lean_ctor_get(x_41, 0);
lean_dec(x_100);
x_101 = !lean_is_exclusive(x_42);
if (x_101 == 0)
{
uint8_t x_102; uint8_t x_103; 
x_102 = 1;
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_102);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_102);
x_103 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_42);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_103);
return x_1;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; uint8_t x_110; 
x_104 = lean_ctor_get(x_42, 0);
x_105 = lean_ctor_get(x_42, 1);
x_106 = lean_ctor_get(x_42, 2);
x_107 = lean_ctor_get(x_42, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_42);
x_108 = 1;
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_105);
lean_ctor_set(x_109, 2, x_106);
lean_ctor_set(x_109, 3, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_108);
x_110 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_110);
return x_1;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_111 = lean_ctor_get(x_41, 1);
x_112 = lean_ctor_get(x_41, 2);
x_113 = lean_ctor_get(x_41, 3);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_41);
x_114 = lean_ctor_get(x_42, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_42, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_42, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_42, 3);
lean_inc(x_117);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_118 = x_42;
} else {
 lean_dec_ref(x_42);
 x_118 = lean_box(0);
}
x_119 = 1;
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(1, 4, 1);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_114);
lean_ctor_set(x_120, 1, x_115);
lean_ctor_set(x_120, 2, x_116);
lean_ctor_set(x_120, 3, x_117);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_119);
x_121 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_121, 0, x_113);
lean_ctor_set(x_121, 1, x_34);
lean_ctor_set(x_121, 2, x_35);
lean_ctor_set(x_121, 3, x_36);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_119);
x_122 = 0;
lean_ctor_set(x_1, 3, x_121);
lean_ctor_set(x_1, 2, x_112);
lean_ctor_set(x_1, 1, x_111);
lean_ctor_set(x_1, 0, x_120);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_122);
return x_1;
}
}
else
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_41, 3);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_41);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_41, 3);
lean_dec(x_125);
x_126 = lean_ctor_get(x_41, 0);
lean_dec(x_126);
x_127 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_127);
x_128 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_128);
return x_1;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_41, 1);
x_130 = lean_ctor_get(x_41, 2);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_41);
x_131 = 0;
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_42);
lean_ctor_set(x_132, 1, x_129);
lean_ctor_set(x_132, 2, x_130);
lean_ctor_set(x_132, 3, x_123);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_131);
x_133 = 1;
lean_ctor_set(x_1, 0, x_132);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_133);
return x_1;
}
}
else
{
uint8_t x_134; 
x_134 = lean_ctor_get_uint8(x_123, sizeof(void*)*4);
if (x_134 == 0)
{
uint8_t x_135; 
lean_free_object(x_1);
x_135 = !lean_is_exclusive(x_41);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_41, 1);
x_137 = lean_ctor_get(x_41, 2);
x_138 = lean_ctor_get(x_41, 3);
lean_dec(x_138);
x_139 = lean_ctor_get(x_41, 0);
lean_dec(x_139);
x_140 = !lean_is_exclusive(x_123);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; 
x_141 = lean_ctor_get(x_123, 0);
x_142 = lean_ctor_get(x_123, 1);
x_143 = lean_ctor_get(x_123, 2);
x_144 = lean_ctor_get(x_123, 3);
x_145 = 1;
lean_inc(x_42);
lean_ctor_set(x_123, 3, x_141);
lean_ctor_set(x_123, 2, x_137);
lean_ctor_set(x_123, 1, x_136);
lean_ctor_set(x_123, 0, x_42);
x_146 = !lean_is_exclusive(x_42);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_147 = lean_ctor_get(x_42, 3);
lean_dec(x_147);
x_148 = lean_ctor_get(x_42, 2);
lean_dec(x_148);
x_149 = lean_ctor_get(x_42, 1);
lean_dec(x_149);
x_150 = lean_ctor_get(x_42, 0);
lean_dec(x_150);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_145);
lean_ctor_set(x_42, 3, x_36);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 0, x_144);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_145);
x_151 = 0;
lean_ctor_set(x_41, 3, x_42);
lean_ctor_set(x_41, 2, x_143);
lean_ctor_set(x_41, 1, x_142);
lean_ctor_set(x_41, 0, x_123);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_151);
return x_41;
}
else
{
lean_object* x_152; uint8_t x_153; 
lean_dec(x_42);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_145);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_34);
lean_ctor_set(x_152, 2, x_35);
lean_ctor_set(x_152, 3, x_36);
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_145);
x_153 = 0;
lean_ctor_set(x_41, 3, x_152);
lean_ctor_set(x_41, 2, x_143);
lean_ctor_set(x_41, 1, x_142);
lean_ctor_set(x_41, 0, x_123);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_153);
return x_41;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_154 = lean_ctor_get(x_123, 0);
x_155 = lean_ctor_get(x_123, 1);
x_156 = lean_ctor_get(x_123, 2);
x_157 = lean_ctor_get(x_123, 3);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_123);
x_158 = 1;
lean_inc(x_42);
x_159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_159, 0, x_42);
lean_ctor_set(x_159, 1, x_136);
lean_ctor_set(x_159, 2, x_137);
lean_ctor_set(x_159, 3, x_154);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_160 = x_42;
} else {
 lean_dec_ref(x_42);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_158);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_157);
lean_ctor_set(x_161, 1, x_34);
lean_ctor_set(x_161, 2, x_35);
lean_ctor_set(x_161, 3, x_36);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_158);
x_162 = 0;
lean_ctor_set(x_41, 3, x_161);
lean_ctor_set(x_41, 2, x_156);
lean_ctor_set(x_41, 1, x_155);
lean_ctor_set(x_41, 0, x_159);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_162);
return x_41;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; 
x_163 = lean_ctor_get(x_41, 1);
x_164 = lean_ctor_get(x_41, 2);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_41);
x_165 = lean_ctor_get(x_123, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_123, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_123, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_123, 3);
lean_inc(x_168);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 x_169 = x_123;
} else {
 lean_dec_ref(x_123);
 x_169 = lean_box(0);
}
x_170 = 1;
lean_inc(x_42);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(1, 4, 1);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_42);
lean_ctor_set(x_171, 1, x_163);
lean_ctor_set(x_171, 2, x_164);
lean_ctor_set(x_171, 3, x_165);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_172 = x_42;
} else {
 lean_dec_ref(x_42);
 x_172 = lean_box(0);
}
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_170);
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 4, 1);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_34);
lean_ctor_set(x_173, 2, x_35);
lean_ctor_set(x_173, 3, x_36);
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_170);
x_174 = 0;
x_175 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_166);
lean_ctor_set(x_175, 2, x_167);
lean_ctor_set(x_175, 3, x_173);
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_174);
return x_175;
}
}
else
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_41);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = lean_ctor_get(x_41, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_41, 0);
lean_dec(x_178);
x_179 = !lean_is_exclusive(x_42);
if (x_179 == 0)
{
uint8_t x_180; uint8_t x_181; 
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_134);
x_180 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_180);
x_181 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_181);
return x_1;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_188; 
x_182 = lean_ctor_get(x_42, 0);
x_183 = lean_ctor_get(x_42, 1);
x_184 = lean_ctor_get(x_42, 2);
x_185 = lean_ctor_get(x_42, 3);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_42);
x_186 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_183);
lean_ctor_set(x_186, 2, x_184);
lean_ctor_set(x_186, 3, x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_134);
x_187 = 0;
lean_ctor_set(x_41, 0, x_186);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_187);
x_188 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; uint8_t x_199; 
x_189 = lean_ctor_get(x_41, 1);
x_190 = lean_ctor_get(x_41, 2);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_41);
x_191 = lean_ctor_get(x_42, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_42, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_42, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_42, 3);
lean_inc(x_194);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_195 = x_42;
} else {
 lean_dec_ref(x_42);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 4, 1);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_191);
lean_ctor_set(x_196, 1, x_192);
lean_ctor_set(x_196, 2, x_193);
lean_ctor_set(x_196, 3, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_134);
x_197 = 0;
x_198 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_189);
lean_ctor_set(x_198, 2, x_190);
lean_ctor_set(x_198, 3, x_123);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_197);
x_199 = 1;
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
}
}
}
}
}
case 1:
{
uint8_t x_200; 
lean_dec(x_35);
lean_dec(x_34);
x_200 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
default: 
{
uint8_t x_201; 
x_201 = l_Std_RBNode_isRed___rarg(x_36);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_36, x_2, x_3);
x_203 = 1;
lean_ctor_set(x_1, 3, x_202);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_203);
return x_1;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_36, x_2, x_3);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_204, 3);
lean_inc(x_206);
if (lean_obj_tag(x_206) == 0)
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_204);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_211; 
x_208 = lean_ctor_get(x_204, 3);
lean_dec(x_208);
x_209 = lean_ctor_get(x_204, 0);
lean_dec(x_209);
x_210 = 0;
lean_ctor_set(x_204, 0, x_206);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_210);
x_211 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_211);
return x_1;
}
else
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; uint8_t x_216; 
x_212 = lean_ctor_get(x_204, 1);
x_213 = lean_ctor_get(x_204, 2);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_204);
x_214 = 0;
x_215 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_215, 0, x_206);
lean_ctor_set(x_215, 1, x_212);
lean_ctor_set(x_215, 2, x_213);
lean_ctor_set(x_215, 3, x_206);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_214);
x_216 = 1;
lean_ctor_set(x_1, 3, x_215);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_216);
return x_1;
}
}
else
{
uint8_t x_217; 
x_217 = lean_ctor_get_uint8(x_206, sizeof(void*)*4);
if (x_217 == 0)
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_204);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_219 = lean_ctor_get(x_204, 1);
x_220 = lean_ctor_get(x_204, 2);
x_221 = lean_ctor_get(x_204, 3);
lean_dec(x_221);
x_222 = lean_ctor_get(x_204, 0);
lean_dec(x_222);
x_223 = !lean_is_exclusive(x_206);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_229; 
x_224 = lean_ctor_get(x_206, 0);
x_225 = lean_ctor_get(x_206, 1);
x_226 = lean_ctor_get(x_206, 2);
x_227 = lean_ctor_get(x_206, 3);
x_228 = 1;
lean_ctor_set(x_206, 3, x_205);
lean_ctor_set(x_206, 2, x_35);
lean_ctor_set(x_206, 1, x_34);
lean_ctor_set(x_206, 0, x_33);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_228);
lean_ctor_set(x_204, 3, x_227);
lean_ctor_set(x_204, 2, x_226);
lean_ctor_set(x_204, 1, x_225);
lean_ctor_set(x_204, 0, x_224);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_228);
x_229 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_229);
return x_1;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; uint8_t x_236; 
x_230 = lean_ctor_get(x_206, 0);
x_231 = lean_ctor_get(x_206, 1);
x_232 = lean_ctor_get(x_206, 2);
x_233 = lean_ctor_get(x_206, 3);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_206);
x_234 = 1;
x_235 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_235, 0, x_33);
lean_ctor_set(x_235, 1, x_34);
lean_ctor_set(x_235, 2, x_35);
lean_ctor_set(x_235, 3, x_205);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_234);
lean_ctor_set(x_204, 3, x_233);
lean_ctor_set(x_204, 2, x_232);
lean_ctor_set(x_204, 1, x_231);
lean_ctor_set(x_204, 0, x_230);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_234);
x_236 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_237 = lean_ctor_get(x_204, 1);
x_238 = lean_ctor_get(x_204, 2);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_204);
x_239 = lean_ctor_get(x_206, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_206, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_206, 2);
lean_inc(x_241);
x_242 = lean_ctor_get(x_206, 3);
lean_inc(x_242);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 lean_ctor_release(x_206, 2);
 lean_ctor_release(x_206, 3);
 x_243 = x_206;
} else {
 lean_dec_ref(x_206);
 x_243 = lean_box(0);
}
x_244 = 1;
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(1, 4, 1);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_33);
lean_ctor_set(x_245, 1, x_34);
lean_ctor_set(x_245, 2, x_35);
lean_ctor_set(x_245, 3, x_205);
lean_ctor_set_uint8(x_245, sizeof(void*)*4, x_244);
x_246 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_246, 0, x_239);
lean_ctor_set(x_246, 1, x_240);
lean_ctor_set(x_246, 2, x_241);
lean_ctor_set(x_246, 3, x_242);
lean_ctor_set_uint8(x_246, sizeof(void*)*4, x_244);
x_247 = 0;
lean_ctor_set(x_1, 3, x_246);
lean_ctor_set(x_1, 2, x_238);
lean_ctor_set(x_1, 1, x_237);
lean_ctor_set(x_1, 0, x_245);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_247);
return x_1;
}
}
else
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_204);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; 
x_249 = lean_ctor_get(x_204, 3);
lean_dec(x_249);
x_250 = lean_ctor_get(x_204, 0);
lean_dec(x_250);
x_251 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_251);
x_252 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_252);
return x_1;
}
else
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; uint8_t x_257; 
x_253 = lean_ctor_get(x_204, 1);
x_254 = lean_ctor_get(x_204, 2);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_204);
x_255 = 0;
x_256 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_256, 0, x_205);
lean_ctor_set(x_256, 1, x_253);
lean_ctor_set(x_256, 2, x_254);
lean_ctor_set(x_256, 3, x_206);
lean_ctor_set_uint8(x_256, sizeof(void*)*4, x_255);
x_257 = 1;
lean_ctor_set(x_1, 3, x_256);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_257);
return x_1;
}
}
}
}
else
{
uint8_t x_258; 
x_258 = lean_ctor_get_uint8(x_205, sizeof(void*)*4);
if (x_258 == 0)
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_204);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_204, 0);
lean_dec(x_260);
x_261 = !lean_is_exclusive(x_205);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_267; 
x_262 = lean_ctor_get(x_205, 0);
x_263 = lean_ctor_get(x_205, 1);
x_264 = lean_ctor_get(x_205, 2);
x_265 = lean_ctor_get(x_205, 3);
x_266 = 1;
lean_ctor_set(x_205, 3, x_262);
lean_ctor_set(x_205, 2, x_35);
lean_ctor_set(x_205, 1, x_34);
lean_ctor_set(x_205, 0, x_33);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_266);
lean_ctor_set(x_204, 0, x_265);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_266);
x_267 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_264);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_205);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_267);
return x_1;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; uint8_t x_274; 
x_268 = lean_ctor_get(x_205, 0);
x_269 = lean_ctor_get(x_205, 1);
x_270 = lean_ctor_get(x_205, 2);
x_271 = lean_ctor_get(x_205, 3);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_205);
x_272 = 1;
x_273 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_273, 0, x_33);
lean_ctor_set(x_273, 1, x_34);
lean_ctor_set(x_273, 2, x_35);
lean_ctor_set(x_273, 3, x_268);
lean_ctor_set_uint8(x_273, sizeof(void*)*4, x_272);
lean_ctor_set(x_204, 0, x_271);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_272);
x_274 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_270);
lean_ctor_set(x_1, 1, x_269);
lean_ctor_set(x_1, 0, x_273);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_274);
return x_1;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_275 = lean_ctor_get(x_204, 1);
x_276 = lean_ctor_get(x_204, 2);
x_277 = lean_ctor_get(x_204, 3);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_204);
x_278 = lean_ctor_get(x_205, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_205, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_205, 2);
lean_inc(x_280);
x_281 = lean_ctor_get(x_205, 3);
lean_inc(x_281);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_282 = x_205;
} else {
 lean_dec_ref(x_205);
 x_282 = lean_box(0);
}
x_283 = 1;
if (lean_is_scalar(x_282)) {
 x_284 = lean_alloc_ctor(1, 4, 1);
} else {
 x_284 = x_282;
}
lean_ctor_set(x_284, 0, x_33);
lean_ctor_set(x_284, 1, x_34);
lean_ctor_set(x_284, 2, x_35);
lean_ctor_set(x_284, 3, x_278);
lean_ctor_set_uint8(x_284, sizeof(void*)*4, x_283);
x_285 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_285, 0, x_281);
lean_ctor_set(x_285, 1, x_275);
lean_ctor_set(x_285, 2, x_276);
lean_ctor_set(x_285, 3, x_277);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_283);
x_286 = 0;
lean_ctor_set(x_1, 3, x_285);
lean_ctor_set(x_1, 2, x_280);
lean_ctor_set(x_1, 1, x_279);
lean_ctor_set(x_1, 0, x_284);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_286);
return x_1;
}
}
else
{
lean_object* x_287; 
x_287 = lean_ctor_get(x_204, 3);
lean_inc(x_287);
if (lean_obj_tag(x_287) == 0)
{
uint8_t x_288; 
x_288 = !lean_is_exclusive(x_204);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; uint8_t x_291; uint8_t x_292; 
x_289 = lean_ctor_get(x_204, 3);
lean_dec(x_289);
x_290 = lean_ctor_get(x_204, 0);
lean_dec(x_290);
x_291 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_291);
x_292 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_292);
return x_1;
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; uint8_t x_297; 
x_293 = lean_ctor_get(x_204, 1);
x_294 = lean_ctor_get(x_204, 2);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_204);
x_295 = 0;
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_205);
lean_ctor_set(x_296, 1, x_293);
lean_ctor_set(x_296, 2, x_294);
lean_ctor_set(x_296, 3, x_287);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_295);
x_297 = 1;
lean_ctor_set(x_1, 3, x_296);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_297);
return x_1;
}
}
else
{
uint8_t x_298; 
x_298 = lean_ctor_get_uint8(x_287, sizeof(void*)*4);
if (x_298 == 0)
{
uint8_t x_299; 
lean_free_object(x_1);
x_299 = !lean_is_exclusive(x_204);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_300 = lean_ctor_get(x_204, 3);
lean_dec(x_300);
x_301 = lean_ctor_get(x_204, 0);
lean_dec(x_301);
x_302 = !lean_is_exclusive(x_287);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; uint8_t x_308; 
x_303 = lean_ctor_get(x_287, 0);
x_304 = lean_ctor_get(x_287, 1);
x_305 = lean_ctor_get(x_287, 2);
x_306 = lean_ctor_get(x_287, 3);
x_307 = 1;
lean_inc(x_205);
lean_ctor_set(x_287, 3, x_205);
lean_ctor_set(x_287, 2, x_35);
lean_ctor_set(x_287, 1, x_34);
lean_ctor_set(x_287, 0, x_33);
x_308 = !lean_is_exclusive(x_205);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_309 = lean_ctor_get(x_205, 3);
lean_dec(x_309);
x_310 = lean_ctor_get(x_205, 2);
lean_dec(x_310);
x_311 = lean_ctor_get(x_205, 1);
lean_dec(x_311);
x_312 = lean_ctor_get(x_205, 0);
lean_dec(x_312);
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_307);
lean_ctor_set(x_205, 3, x_306);
lean_ctor_set(x_205, 2, x_305);
lean_ctor_set(x_205, 1, x_304);
lean_ctor_set(x_205, 0, x_303);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_307);
x_313 = 0;
lean_ctor_set(x_204, 3, x_205);
lean_ctor_set(x_204, 0, x_287);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_313);
return x_204;
}
else
{
lean_object* x_314; uint8_t x_315; 
lean_dec(x_205);
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_307);
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_303);
lean_ctor_set(x_314, 1, x_304);
lean_ctor_set(x_314, 2, x_305);
lean_ctor_set(x_314, 3, x_306);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_307);
x_315 = 0;
lean_ctor_set(x_204, 3, x_314);
lean_ctor_set(x_204, 0, x_287);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_315);
return x_204;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_316 = lean_ctor_get(x_287, 0);
x_317 = lean_ctor_get(x_287, 1);
x_318 = lean_ctor_get(x_287, 2);
x_319 = lean_ctor_get(x_287, 3);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_287);
x_320 = 1;
lean_inc(x_205);
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_33);
lean_ctor_set(x_321, 1, x_34);
lean_ctor_set(x_321, 2, x_35);
lean_ctor_set(x_321, 3, x_205);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_322 = x_205;
} else {
 lean_dec_ref(x_205);
 x_322 = lean_box(0);
}
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_320);
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 4, 1);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_316);
lean_ctor_set(x_323, 1, x_317);
lean_ctor_set(x_323, 2, x_318);
lean_ctor_set(x_323, 3, x_319);
lean_ctor_set_uint8(x_323, sizeof(void*)*4, x_320);
x_324 = 0;
lean_ctor_set(x_204, 3, x_323);
lean_ctor_set(x_204, 0, x_321);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_324);
return x_204;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; 
x_325 = lean_ctor_get(x_204, 1);
x_326 = lean_ctor_get(x_204, 2);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_204);
x_327 = lean_ctor_get(x_287, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_287, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_287, 2);
lean_inc(x_329);
x_330 = lean_ctor_get(x_287, 3);
lean_inc(x_330);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 lean_ctor_release(x_287, 2);
 lean_ctor_release(x_287, 3);
 x_331 = x_287;
} else {
 lean_dec_ref(x_287);
 x_331 = lean_box(0);
}
x_332 = 1;
lean_inc(x_205);
if (lean_is_scalar(x_331)) {
 x_333 = lean_alloc_ctor(1, 4, 1);
} else {
 x_333 = x_331;
}
lean_ctor_set(x_333, 0, x_33);
lean_ctor_set(x_333, 1, x_34);
lean_ctor_set(x_333, 2, x_35);
lean_ctor_set(x_333, 3, x_205);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_334 = x_205;
} else {
 lean_dec_ref(x_205);
 x_334 = lean_box(0);
}
lean_ctor_set_uint8(x_333, sizeof(void*)*4, x_332);
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 4, 1);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_327);
lean_ctor_set(x_335, 1, x_328);
lean_ctor_set(x_335, 2, x_329);
lean_ctor_set(x_335, 3, x_330);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_332);
x_336 = 0;
x_337 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_337, 0, x_333);
lean_ctor_set(x_337, 1, x_325);
lean_ctor_set(x_337, 2, x_326);
lean_ctor_set(x_337, 3, x_335);
lean_ctor_set_uint8(x_337, sizeof(void*)*4, x_336);
return x_337;
}
}
else
{
uint8_t x_338; 
x_338 = !lean_is_exclusive(x_204);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_339 = lean_ctor_get(x_204, 3);
lean_dec(x_339);
x_340 = lean_ctor_get(x_204, 0);
lean_dec(x_340);
x_341 = !lean_is_exclusive(x_205);
if (x_341 == 0)
{
uint8_t x_342; uint8_t x_343; 
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_298);
x_342 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_342);
x_343 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_343);
return x_1;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; uint8_t x_350; 
x_344 = lean_ctor_get(x_205, 0);
x_345 = lean_ctor_get(x_205, 1);
x_346 = lean_ctor_get(x_205, 2);
x_347 = lean_ctor_get(x_205, 3);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_205);
x_348 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_348, 0, x_344);
lean_ctor_set(x_348, 1, x_345);
lean_ctor_set(x_348, 2, x_346);
lean_ctor_set(x_348, 3, x_347);
lean_ctor_set_uint8(x_348, sizeof(void*)*4, x_298);
x_349 = 0;
lean_ctor_set(x_204, 0, x_348);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_349);
x_350 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_350);
return x_1;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; uint8_t x_361; 
x_351 = lean_ctor_get(x_204, 1);
x_352 = lean_ctor_get(x_204, 2);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_204);
x_353 = lean_ctor_get(x_205, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_205, 1);
lean_inc(x_354);
x_355 = lean_ctor_get(x_205, 2);
lean_inc(x_355);
x_356 = lean_ctor_get(x_205, 3);
lean_inc(x_356);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_357 = x_205;
} else {
 lean_dec_ref(x_205);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 4, 1);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_353);
lean_ctor_set(x_358, 1, x_354);
lean_ctor_set(x_358, 2, x_355);
lean_ctor_set(x_358, 3, x_356);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_298);
x_359 = 0;
x_360 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_351);
lean_ctor_set(x_360, 2, x_352);
lean_ctor_set(x_360, 3, x_287);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
x_361 = 1;
lean_ctor_set(x_1, 3, x_360);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_361);
return x_1;
}
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
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_362 = lean_ctor_get(x_1, 0);
x_363 = lean_ctor_get(x_1, 1);
x_364 = lean_ctor_get(x_1, 2);
x_365 = lean_ctor_get(x_1, 3);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_1);
x_366 = l_Lean_Name_quickCmp(x_2, x_363);
switch (x_366) {
case 0:
{
uint8_t x_367; 
x_367 = l_Std_RBNode_isRed___rarg(x_362);
if (x_367 == 0)
{
lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_368 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_362, x_2, x_3);
x_369 = 1;
x_370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_363);
lean_ctor_set(x_370, 2, x_364);
lean_ctor_set(x_370, 3, x_365);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_369);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; 
x_371 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_362, x_2, x_3);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; 
x_373 = lean_ctor_get(x_371, 3);
lean_inc(x_373);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; 
x_374 = lean_ctor_get(x_371, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_371, 2);
lean_inc(x_375);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_376 = x_371;
} else {
 lean_dec_ref(x_371);
 x_376 = lean_box(0);
}
x_377 = 0;
if (lean_is_scalar(x_376)) {
 x_378 = lean_alloc_ctor(1, 4, 1);
} else {
 x_378 = x_376;
}
lean_ctor_set(x_378, 0, x_373);
lean_ctor_set(x_378, 1, x_374);
lean_ctor_set(x_378, 2, x_375);
lean_ctor_set(x_378, 3, x_373);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_377);
x_379 = 1;
x_380 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_363);
lean_ctor_set(x_380, 2, x_364);
lean_ctor_set(x_380, 3, x_365);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_379);
return x_380;
}
else
{
uint8_t x_381; 
x_381 = lean_ctor_get_uint8(x_373, sizeof(void*)*4);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; 
x_382 = lean_ctor_get(x_371, 1);
lean_inc(x_382);
x_383 = lean_ctor_get(x_371, 2);
lean_inc(x_383);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_384 = x_371;
} else {
 lean_dec_ref(x_371);
 x_384 = lean_box(0);
}
x_385 = lean_ctor_get(x_373, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_373, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_373, 2);
lean_inc(x_387);
x_388 = lean_ctor_get(x_373, 3);
lean_inc(x_388);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 lean_ctor_release(x_373, 2);
 lean_ctor_release(x_373, 3);
 x_389 = x_373;
} else {
 lean_dec_ref(x_373);
 x_389 = lean_box(0);
}
x_390 = 1;
if (lean_is_scalar(x_389)) {
 x_391 = lean_alloc_ctor(1, 4, 1);
} else {
 x_391 = x_389;
}
lean_ctor_set(x_391, 0, x_372);
lean_ctor_set(x_391, 1, x_382);
lean_ctor_set(x_391, 2, x_383);
lean_ctor_set(x_391, 3, x_385);
lean_ctor_set_uint8(x_391, sizeof(void*)*4, x_390);
if (lean_is_scalar(x_384)) {
 x_392 = lean_alloc_ctor(1, 4, 1);
} else {
 x_392 = x_384;
}
lean_ctor_set(x_392, 0, x_388);
lean_ctor_set(x_392, 1, x_363);
lean_ctor_set(x_392, 2, x_364);
lean_ctor_set(x_392, 3, x_365);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_390);
x_393 = 0;
x_394 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_386);
lean_ctor_set(x_394, 2, x_387);
lean_ctor_set(x_394, 3, x_392);
lean_ctor_set_uint8(x_394, sizeof(void*)*4, x_393);
return x_394;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; 
x_395 = lean_ctor_get(x_371, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_371, 2);
lean_inc(x_396);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_397 = x_371;
} else {
 lean_dec_ref(x_371);
 x_397 = lean_box(0);
}
x_398 = 0;
if (lean_is_scalar(x_397)) {
 x_399 = lean_alloc_ctor(1, 4, 1);
} else {
 x_399 = x_397;
}
lean_ctor_set(x_399, 0, x_372);
lean_ctor_set(x_399, 1, x_395);
lean_ctor_set(x_399, 2, x_396);
lean_ctor_set(x_399, 3, x_373);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_398);
x_400 = 1;
x_401 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_363);
lean_ctor_set(x_401, 2, x_364);
lean_ctor_set(x_401, 3, x_365);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_400);
return x_401;
}
}
}
else
{
uint8_t x_402; 
x_402 = lean_ctor_get_uint8(x_372, sizeof(void*)*4);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; lean_object* x_416; 
x_403 = lean_ctor_get(x_371, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_371, 2);
lean_inc(x_404);
x_405 = lean_ctor_get(x_371, 3);
lean_inc(x_405);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_406 = x_371;
} else {
 lean_dec_ref(x_371);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_372, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_372, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_372, 2);
lean_inc(x_409);
x_410 = lean_ctor_get(x_372, 3);
lean_inc(x_410);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_411 = x_372;
} else {
 lean_dec_ref(x_372);
 x_411 = lean_box(0);
}
x_412 = 1;
if (lean_is_scalar(x_411)) {
 x_413 = lean_alloc_ctor(1, 4, 1);
} else {
 x_413 = x_411;
}
lean_ctor_set(x_413, 0, x_407);
lean_ctor_set(x_413, 1, x_408);
lean_ctor_set(x_413, 2, x_409);
lean_ctor_set(x_413, 3, x_410);
lean_ctor_set_uint8(x_413, sizeof(void*)*4, x_412);
if (lean_is_scalar(x_406)) {
 x_414 = lean_alloc_ctor(1, 4, 1);
} else {
 x_414 = x_406;
}
lean_ctor_set(x_414, 0, x_405);
lean_ctor_set(x_414, 1, x_363);
lean_ctor_set(x_414, 2, x_364);
lean_ctor_set(x_414, 3, x_365);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_412);
x_415 = 0;
x_416 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_416, 0, x_413);
lean_ctor_set(x_416, 1, x_403);
lean_ctor_set(x_416, 2, x_404);
lean_ctor_set(x_416, 3, x_414);
lean_ctor_set_uint8(x_416, sizeof(void*)*4, x_415);
return x_416;
}
else
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_371, 3);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; uint8_t x_423; lean_object* x_424; 
x_418 = lean_ctor_get(x_371, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_371, 2);
lean_inc(x_419);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_420 = x_371;
} else {
 lean_dec_ref(x_371);
 x_420 = lean_box(0);
}
x_421 = 0;
if (lean_is_scalar(x_420)) {
 x_422 = lean_alloc_ctor(1, 4, 1);
} else {
 x_422 = x_420;
}
lean_ctor_set(x_422, 0, x_372);
lean_ctor_set(x_422, 1, x_418);
lean_ctor_set(x_422, 2, x_419);
lean_ctor_set(x_422, 3, x_417);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
x_423 = 1;
x_424 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_363);
lean_ctor_set(x_424, 2, x_364);
lean_ctor_set(x_424, 3, x_365);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_423);
return x_424;
}
else
{
uint8_t x_425; 
x_425 = lean_ctor_get_uint8(x_417, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; 
x_426 = lean_ctor_get(x_371, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_371, 2);
lean_inc(x_427);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_428 = x_371;
} else {
 lean_dec_ref(x_371);
 x_428 = lean_box(0);
}
x_429 = lean_ctor_get(x_417, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_417, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_417, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_417, 3);
lean_inc(x_432);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_433 = x_417;
} else {
 lean_dec_ref(x_417);
 x_433 = lean_box(0);
}
x_434 = 1;
lean_inc(x_372);
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(1, 4, 1);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_372);
lean_ctor_set(x_435, 1, x_426);
lean_ctor_set(x_435, 2, x_427);
lean_ctor_set(x_435, 3, x_429);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_436 = x_372;
} else {
 lean_dec_ref(x_372);
 x_436 = lean_box(0);
}
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_434);
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 4, 1);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_432);
lean_ctor_set(x_437, 1, x_363);
lean_ctor_set(x_437, 2, x_364);
lean_ctor_set(x_437, 3, x_365);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_434);
x_438 = 0;
if (lean_is_scalar(x_428)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_428;
}
lean_ctor_set(x_439, 0, x_435);
lean_ctor_set(x_439, 1, x_430);
lean_ctor_set(x_439, 2, x_431);
lean_ctor_set(x_439, 3, x_437);
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
return x_439;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; 
x_440 = lean_ctor_get(x_371, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_371, 2);
lean_inc(x_441);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_442 = x_371;
} else {
 lean_dec_ref(x_371);
 x_442 = lean_box(0);
}
x_443 = lean_ctor_get(x_372, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_372, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_372, 2);
lean_inc(x_445);
x_446 = lean_ctor_get(x_372, 3);
lean_inc(x_446);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_447 = x_372;
} else {
 lean_dec_ref(x_372);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 4, 1);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_443);
lean_ctor_set(x_448, 1, x_444);
lean_ctor_set(x_448, 2, x_445);
lean_ctor_set(x_448, 3, x_446);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_425);
x_449 = 0;
if (lean_is_scalar(x_442)) {
 x_450 = lean_alloc_ctor(1, 4, 1);
} else {
 x_450 = x_442;
}
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_440);
lean_ctor_set(x_450, 2, x_441);
lean_ctor_set(x_450, 3, x_417);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
x_451 = 1;
x_452 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_452, 0, x_450);
lean_ctor_set(x_452, 1, x_363);
lean_ctor_set(x_452, 2, x_364);
lean_ctor_set(x_452, 3, x_365);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_451);
return x_452;
}
}
}
}
}
}
case 1:
{
uint8_t x_453; lean_object* x_454; 
lean_dec(x_364);
lean_dec(x_363);
x_453 = 1;
x_454 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_454, 0, x_362);
lean_ctor_set(x_454, 1, x_2);
lean_ctor_set(x_454, 2, x_3);
lean_ctor_set(x_454, 3, x_365);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_453);
return x_454;
}
default: 
{
uint8_t x_455; 
x_455 = l_Std_RBNode_isRed___rarg(x_365);
if (x_455 == 0)
{
lean_object* x_456; uint8_t x_457; lean_object* x_458; 
x_456 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_365, x_2, x_3);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_362);
lean_ctor_set(x_458, 1, x_363);
lean_ctor_set(x_458, 2, x_364);
lean_ctor_set(x_458, 3, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
else
{
lean_object* x_459; lean_object* x_460; 
x_459 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_365, x_2, x_3);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; 
x_461 = lean_ctor_get(x_459, 3);
lean_inc(x_461);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; 
x_462 = lean_ctor_get(x_459, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_459, 2);
lean_inc(x_463);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_464 = x_459;
} else {
 lean_dec_ref(x_459);
 x_464 = lean_box(0);
}
x_465 = 0;
if (lean_is_scalar(x_464)) {
 x_466 = lean_alloc_ctor(1, 4, 1);
} else {
 x_466 = x_464;
}
lean_ctor_set(x_466, 0, x_461);
lean_ctor_set(x_466, 1, x_462);
lean_ctor_set(x_466, 2, x_463);
lean_ctor_set(x_466, 3, x_461);
lean_ctor_set_uint8(x_466, sizeof(void*)*4, x_465);
x_467 = 1;
x_468 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_468, 0, x_362);
lean_ctor_set(x_468, 1, x_363);
lean_ctor_set(x_468, 2, x_364);
lean_ctor_set(x_468, 3, x_466);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_467);
return x_468;
}
else
{
uint8_t x_469; 
x_469 = lean_ctor_get_uint8(x_461, sizeof(void*)*4);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; uint8_t x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; lean_object* x_482; 
x_470 = lean_ctor_get(x_459, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_459, 2);
lean_inc(x_471);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_472 = x_459;
} else {
 lean_dec_ref(x_459);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_461, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_461, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_461, 2);
lean_inc(x_475);
x_476 = lean_ctor_get(x_461, 3);
lean_inc(x_476);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 lean_ctor_release(x_461, 2);
 lean_ctor_release(x_461, 3);
 x_477 = x_461;
} else {
 lean_dec_ref(x_461);
 x_477 = lean_box(0);
}
x_478 = 1;
if (lean_is_scalar(x_477)) {
 x_479 = lean_alloc_ctor(1, 4, 1);
} else {
 x_479 = x_477;
}
lean_ctor_set(x_479, 0, x_362);
lean_ctor_set(x_479, 1, x_363);
lean_ctor_set(x_479, 2, x_364);
lean_ctor_set(x_479, 3, x_460);
lean_ctor_set_uint8(x_479, sizeof(void*)*4, x_478);
if (lean_is_scalar(x_472)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_472;
}
lean_ctor_set(x_480, 0, x_473);
lean_ctor_set(x_480, 1, x_474);
lean_ctor_set(x_480, 2, x_475);
lean_ctor_set(x_480, 3, x_476);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_478);
x_481 = 0;
x_482 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_482, 0, x_479);
lean_ctor_set(x_482, 1, x_470);
lean_ctor_set(x_482, 2, x_471);
lean_ctor_set(x_482, 3, x_480);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_481);
return x_482;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; 
x_483 = lean_ctor_get(x_459, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_459, 2);
lean_inc(x_484);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_485 = x_459;
} else {
 lean_dec_ref(x_459);
 x_485 = lean_box(0);
}
x_486 = 0;
if (lean_is_scalar(x_485)) {
 x_487 = lean_alloc_ctor(1, 4, 1);
} else {
 x_487 = x_485;
}
lean_ctor_set(x_487, 0, x_460);
lean_ctor_set(x_487, 1, x_483);
lean_ctor_set(x_487, 2, x_484);
lean_ctor_set(x_487, 3, x_461);
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_486);
x_488 = 1;
x_489 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_489, 0, x_362);
lean_ctor_set(x_489, 1, x_363);
lean_ctor_set(x_489, 2, x_364);
lean_ctor_set(x_489, 3, x_487);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_488);
return x_489;
}
}
}
else
{
uint8_t x_490; 
x_490 = lean_ctor_get_uint8(x_460, sizeof(void*)*4);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; lean_object* x_504; 
x_491 = lean_ctor_get(x_459, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_459, 2);
lean_inc(x_492);
x_493 = lean_ctor_get(x_459, 3);
lean_inc(x_493);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_494 = x_459;
} else {
 lean_dec_ref(x_459);
 x_494 = lean_box(0);
}
x_495 = lean_ctor_get(x_460, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_460, 1);
lean_inc(x_496);
x_497 = lean_ctor_get(x_460, 2);
lean_inc(x_497);
x_498 = lean_ctor_get(x_460, 3);
lean_inc(x_498);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_499 = x_460;
} else {
 lean_dec_ref(x_460);
 x_499 = lean_box(0);
}
x_500 = 1;
if (lean_is_scalar(x_499)) {
 x_501 = lean_alloc_ctor(1, 4, 1);
} else {
 x_501 = x_499;
}
lean_ctor_set(x_501, 0, x_362);
lean_ctor_set(x_501, 1, x_363);
lean_ctor_set(x_501, 2, x_364);
lean_ctor_set(x_501, 3, x_495);
lean_ctor_set_uint8(x_501, sizeof(void*)*4, x_500);
if (lean_is_scalar(x_494)) {
 x_502 = lean_alloc_ctor(1, 4, 1);
} else {
 x_502 = x_494;
}
lean_ctor_set(x_502, 0, x_498);
lean_ctor_set(x_502, 1, x_491);
lean_ctor_set(x_502, 2, x_492);
lean_ctor_set(x_502, 3, x_493);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_500);
x_503 = 0;
x_504 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_496);
lean_ctor_set(x_504, 2, x_497);
lean_ctor_set(x_504, 3, x_502);
lean_ctor_set_uint8(x_504, sizeof(void*)*4, x_503);
return x_504;
}
else
{
lean_object* x_505; 
x_505 = lean_ctor_get(x_459, 3);
lean_inc(x_505);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; uint8_t x_511; lean_object* x_512; 
x_506 = lean_ctor_get(x_459, 1);
lean_inc(x_506);
x_507 = lean_ctor_get(x_459, 2);
lean_inc(x_507);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_508 = x_459;
} else {
 lean_dec_ref(x_459);
 x_508 = lean_box(0);
}
x_509 = 0;
if (lean_is_scalar(x_508)) {
 x_510 = lean_alloc_ctor(1, 4, 1);
} else {
 x_510 = x_508;
}
lean_ctor_set(x_510, 0, x_460);
lean_ctor_set(x_510, 1, x_506);
lean_ctor_set(x_510, 2, x_507);
lean_ctor_set(x_510, 3, x_505);
lean_ctor_set_uint8(x_510, sizeof(void*)*4, x_509);
x_511 = 1;
x_512 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_512, 0, x_362);
lean_ctor_set(x_512, 1, x_363);
lean_ctor_set(x_512, 2, x_364);
lean_ctor_set(x_512, 3, x_510);
lean_ctor_set_uint8(x_512, sizeof(void*)*4, x_511);
return x_512;
}
else
{
uint8_t x_513; 
x_513 = lean_ctor_get_uint8(x_505, sizeof(void*)*4);
if (x_513 == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; 
x_514 = lean_ctor_get(x_459, 1);
lean_inc(x_514);
x_515 = lean_ctor_get(x_459, 2);
lean_inc(x_515);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_516 = x_459;
} else {
 lean_dec_ref(x_459);
 x_516 = lean_box(0);
}
x_517 = lean_ctor_get(x_505, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_505, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_505, 2);
lean_inc(x_519);
x_520 = lean_ctor_get(x_505, 3);
lean_inc(x_520);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 lean_ctor_release(x_505, 2);
 lean_ctor_release(x_505, 3);
 x_521 = x_505;
} else {
 lean_dec_ref(x_505);
 x_521 = lean_box(0);
}
x_522 = 1;
lean_inc(x_460);
if (lean_is_scalar(x_521)) {
 x_523 = lean_alloc_ctor(1, 4, 1);
} else {
 x_523 = x_521;
}
lean_ctor_set(x_523, 0, x_362);
lean_ctor_set(x_523, 1, x_363);
lean_ctor_set(x_523, 2, x_364);
lean_ctor_set(x_523, 3, x_460);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_524 = x_460;
} else {
 lean_dec_ref(x_460);
 x_524 = lean_box(0);
}
lean_ctor_set_uint8(x_523, sizeof(void*)*4, x_522);
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(1, 4, 1);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_517);
lean_ctor_set(x_525, 1, x_518);
lean_ctor_set(x_525, 2, x_519);
lean_ctor_set(x_525, 3, x_520);
lean_ctor_set_uint8(x_525, sizeof(void*)*4, x_522);
x_526 = 0;
if (lean_is_scalar(x_516)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_516;
}
lean_ctor_set(x_527, 0, x_523);
lean_ctor_set(x_527, 1, x_514);
lean_ctor_set(x_527, 2, x_515);
lean_ctor_set(x_527, 3, x_525);
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
return x_527;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; uint8_t x_537; lean_object* x_538; uint8_t x_539; lean_object* x_540; 
x_528 = lean_ctor_get(x_459, 1);
lean_inc(x_528);
x_529 = lean_ctor_get(x_459, 2);
lean_inc(x_529);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_530 = x_459;
} else {
 lean_dec_ref(x_459);
 x_530 = lean_box(0);
}
x_531 = lean_ctor_get(x_460, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_460, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_460, 2);
lean_inc(x_533);
x_534 = lean_ctor_get(x_460, 3);
lean_inc(x_534);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_535 = x_460;
} else {
 lean_dec_ref(x_460);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 4, 1);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_531);
lean_ctor_set(x_536, 1, x_532);
lean_ctor_set(x_536, 2, x_533);
lean_ctor_set(x_536, 3, x_534);
lean_ctor_set_uint8(x_536, sizeof(void*)*4, x_513);
x_537 = 0;
if (lean_is_scalar(x_530)) {
 x_538 = lean_alloc_ctor(1, 4, 1);
} else {
 x_538 = x_530;
}
lean_ctor_set(x_538, 0, x_536);
lean_ctor_set(x_538, 1, x_528);
lean_ctor_set(x_538, 2, x_529);
lean_ctor_set(x_538, 3, x_505);
lean_ctor_set_uint8(x_538, sizeof(void*)*4, x_537);
x_539 = 1;
x_540 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_540, 0, x_362);
lean_ctor_set(x_540, 1, x_363);
lean_ctor_set(x_540, 2, x_364);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_539);
return x_540;
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
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_13 = l_Lean_Name_quickCmp(x_2, x_10);
switch (x_13) {
case 0:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_9, x_2, x_3);
x_15 = 0;
lean_ctor_set(x_1, 0, x_14);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
case 1:
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
default: 
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_12, x_2, x_3);
x_18 = 0;
lean_ctor_set(x_1, 3, x_17);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_18);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_23 = l_Lean_Name_quickCmp(x_2, x_20);
switch (x_23) {
case 0:
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_19, x_2, x_3);
x_25 = 0;
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_25);
return x_26;
}
case 1:
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
default: 
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_22, x_2, x_3);
x_30 = 0;
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 2);
x_36 = lean_ctor_get(x_1, 3);
x_37 = l_Lean_Name_quickCmp(x_2, x_34);
switch (x_37) {
case 0:
{
uint8_t x_38; 
x_38 = l_Std_RBNode_isRed___rarg(x_33);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_33, x_2, x_3);
x_40 = 1;
lean_ctor_set(x_1, 0, x_39);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_40);
return x_1;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_33, x_2, x_3);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 3);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_41, 3);
lean_dec(x_45);
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = 0;
lean_ctor_set(x_41, 0, x_43);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_47);
x_48 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_41, 1);
x_50 = lean_ctor_get(x_41, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = 0;
x_52 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 2, x_50);
lean_ctor_set(x_52, 3, x_43);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_51);
x_53 = 1;
lean_ctor_set(x_1, 0, x_52);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_53);
return x_1;
}
}
else
{
uint8_t x_54; 
x_54 = lean_ctor_get_uint8(x_43, sizeof(void*)*4);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_41);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_41, 1);
x_57 = lean_ctor_get(x_41, 2);
x_58 = lean_ctor_get(x_41, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_41, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_43);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_43, 0);
x_62 = lean_ctor_get(x_43, 1);
x_63 = lean_ctor_get(x_43, 2);
x_64 = lean_ctor_get(x_43, 3);
x_65 = 1;
lean_ctor_set(x_43, 3, x_61);
lean_ctor_set(x_43, 2, x_57);
lean_ctor_set(x_43, 1, x_56);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_65);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_64);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_65);
x_66 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_63);
lean_ctor_set(x_1, 1, x_62);
lean_ctor_set(x_1, 0, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; 
x_67 = lean_ctor_get(x_43, 0);
x_68 = lean_ctor_get(x_43, 1);
x_69 = lean_ctor_get(x_43, 2);
x_70 = lean_ctor_get(x_43, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_43);
x_71 = 1;
x_72 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_72, 0, x_42);
lean_ctor_set(x_72, 1, x_56);
lean_ctor_set(x_72, 2, x_57);
lean_ctor_set(x_72, 3, x_67);
lean_ctor_set_uint8(x_72, sizeof(void*)*4, x_71);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_70);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_71);
x_73 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_69);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_72);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_73);
return x_1;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_74 = lean_ctor_get(x_41, 1);
x_75 = lean_ctor_get(x_41, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_41);
x_76 = lean_ctor_get(x_43, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_43, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_43, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_43, 3);
lean_inc(x_79);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_80 = x_43;
} else {
 lean_dec_ref(x_43);
 x_80 = lean_box(0);
}
x_81 = 1;
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(1, 4, 1);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_42);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_75);
lean_ctor_set(x_82, 3, x_76);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_81);
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_34);
lean_ctor_set(x_83, 2, x_35);
lean_ctor_set(x_83, 3, x_36);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_81);
x_84 = 0;
lean_ctor_set(x_1, 3, x_83);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_82);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_84);
return x_1;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_41);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_41, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_41, 0);
lean_dec(x_87);
x_88 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_88);
x_89 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_89);
return x_1;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_41, 1);
x_91 = lean_ctor_get(x_41, 2);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_41);
x_92 = 0;
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_42);
lean_ctor_set(x_93, 1, x_90);
lean_ctor_set(x_93, 2, x_91);
lean_ctor_set(x_93, 3, x_43);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_92);
x_94 = 1;
lean_ctor_set(x_1, 0, x_93);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_94);
return x_1;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_42, sizeof(void*)*4);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_41);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_41, 1);
x_98 = lean_ctor_get(x_41, 2);
x_99 = lean_ctor_get(x_41, 3);
x_100 = lean_ctor_get(x_41, 0);
lean_dec(x_100);
x_101 = !lean_is_exclusive(x_42);
if (x_101 == 0)
{
uint8_t x_102; uint8_t x_103; 
x_102 = 1;
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_102);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_102);
x_103 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_42);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_103);
return x_1;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; uint8_t x_110; 
x_104 = lean_ctor_get(x_42, 0);
x_105 = lean_ctor_get(x_42, 1);
x_106 = lean_ctor_get(x_42, 2);
x_107 = lean_ctor_get(x_42, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_42);
x_108 = 1;
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_105);
lean_ctor_set(x_109, 2, x_106);
lean_ctor_set(x_109, 3, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_108);
x_110 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_110);
return x_1;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_111 = lean_ctor_get(x_41, 1);
x_112 = lean_ctor_get(x_41, 2);
x_113 = lean_ctor_get(x_41, 3);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_41);
x_114 = lean_ctor_get(x_42, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_42, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_42, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_42, 3);
lean_inc(x_117);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_118 = x_42;
} else {
 lean_dec_ref(x_42);
 x_118 = lean_box(0);
}
x_119 = 1;
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(1, 4, 1);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_114);
lean_ctor_set(x_120, 1, x_115);
lean_ctor_set(x_120, 2, x_116);
lean_ctor_set(x_120, 3, x_117);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_119);
x_121 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_121, 0, x_113);
lean_ctor_set(x_121, 1, x_34);
lean_ctor_set(x_121, 2, x_35);
lean_ctor_set(x_121, 3, x_36);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_119);
x_122 = 0;
lean_ctor_set(x_1, 3, x_121);
lean_ctor_set(x_1, 2, x_112);
lean_ctor_set(x_1, 1, x_111);
lean_ctor_set(x_1, 0, x_120);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_122);
return x_1;
}
}
else
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_41, 3);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_41);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_41, 3);
lean_dec(x_125);
x_126 = lean_ctor_get(x_41, 0);
lean_dec(x_126);
x_127 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_127);
x_128 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_128);
return x_1;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_41, 1);
x_130 = lean_ctor_get(x_41, 2);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_41);
x_131 = 0;
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_42);
lean_ctor_set(x_132, 1, x_129);
lean_ctor_set(x_132, 2, x_130);
lean_ctor_set(x_132, 3, x_123);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_131);
x_133 = 1;
lean_ctor_set(x_1, 0, x_132);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_133);
return x_1;
}
}
else
{
uint8_t x_134; 
x_134 = lean_ctor_get_uint8(x_123, sizeof(void*)*4);
if (x_134 == 0)
{
uint8_t x_135; 
lean_free_object(x_1);
x_135 = !lean_is_exclusive(x_41);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_41, 1);
x_137 = lean_ctor_get(x_41, 2);
x_138 = lean_ctor_get(x_41, 3);
lean_dec(x_138);
x_139 = lean_ctor_get(x_41, 0);
lean_dec(x_139);
x_140 = !lean_is_exclusive(x_123);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; 
x_141 = lean_ctor_get(x_123, 0);
x_142 = lean_ctor_get(x_123, 1);
x_143 = lean_ctor_get(x_123, 2);
x_144 = lean_ctor_get(x_123, 3);
x_145 = 1;
lean_inc(x_42);
lean_ctor_set(x_123, 3, x_141);
lean_ctor_set(x_123, 2, x_137);
lean_ctor_set(x_123, 1, x_136);
lean_ctor_set(x_123, 0, x_42);
x_146 = !lean_is_exclusive(x_42);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_147 = lean_ctor_get(x_42, 3);
lean_dec(x_147);
x_148 = lean_ctor_get(x_42, 2);
lean_dec(x_148);
x_149 = lean_ctor_get(x_42, 1);
lean_dec(x_149);
x_150 = lean_ctor_get(x_42, 0);
lean_dec(x_150);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_145);
lean_ctor_set(x_42, 3, x_36);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 0, x_144);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_145);
x_151 = 0;
lean_ctor_set(x_41, 3, x_42);
lean_ctor_set(x_41, 2, x_143);
lean_ctor_set(x_41, 1, x_142);
lean_ctor_set(x_41, 0, x_123);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_151);
return x_41;
}
else
{
lean_object* x_152; uint8_t x_153; 
lean_dec(x_42);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_145);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_34);
lean_ctor_set(x_152, 2, x_35);
lean_ctor_set(x_152, 3, x_36);
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_145);
x_153 = 0;
lean_ctor_set(x_41, 3, x_152);
lean_ctor_set(x_41, 2, x_143);
lean_ctor_set(x_41, 1, x_142);
lean_ctor_set(x_41, 0, x_123);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_153);
return x_41;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_154 = lean_ctor_get(x_123, 0);
x_155 = lean_ctor_get(x_123, 1);
x_156 = lean_ctor_get(x_123, 2);
x_157 = lean_ctor_get(x_123, 3);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_123);
x_158 = 1;
lean_inc(x_42);
x_159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_159, 0, x_42);
lean_ctor_set(x_159, 1, x_136);
lean_ctor_set(x_159, 2, x_137);
lean_ctor_set(x_159, 3, x_154);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_160 = x_42;
} else {
 lean_dec_ref(x_42);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_158);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_157);
lean_ctor_set(x_161, 1, x_34);
lean_ctor_set(x_161, 2, x_35);
lean_ctor_set(x_161, 3, x_36);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_158);
x_162 = 0;
lean_ctor_set(x_41, 3, x_161);
lean_ctor_set(x_41, 2, x_156);
lean_ctor_set(x_41, 1, x_155);
lean_ctor_set(x_41, 0, x_159);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_162);
return x_41;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; 
x_163 = lean_ctor_get(x_41, 1);
x_164 = lean_ctor_get(x_41, 2);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_41);
x_165 = lean_ctor_get(x_123, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_123, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_123, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_123, 3);
lean_inc(x_168);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 x_169 = x_123;
} else {
 lean_dec_ref(x_123);
 x_169 = lean_box(0);
}
x_170 = 1;
lean_inc(x_42);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(1, 4, 1);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_42);
lean_ctor_set(x_171, 1, x_163);
lean_ctor_set(x_171, 2, x_164);
lean_ctor_set(x_171, 3, x_165);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_172 = x_42;
} else {
 lean_dec_ref(x_42);
 x_172 = lean_box(0);
}
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_170);
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 4, 1);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_34);
lean_ctor_set(x_173, 2, x_35);
lean_ctor_set(x_173, 3, x_36);
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_170);
x_174 = 0;
x_175 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_166);
lean_ctor_set(x_175, 2, x_167);
lean_ctor_set(x_175, 3, x_173);
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_174);
return x_175;
}
}
else
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_41);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = lean_ctor_get(x_41, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_41, 0);
lean_dec(x_178);
x_179 = !lean_is_exclusive(x_42);
if (x_179 == 0)
{
uint8_t x_180; uint8_t x_181; 
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_134);
x_180 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_180);
x_181 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_181);
return x_1;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_188; 
x_182 = lean_ctor_get(x_42, 0);
x_183 = lean_ctor_get(x_42, 1);
x_184 = lean_ctor_get(x_42, 2);
x_185 = lean_ctor_get(x_42, 3);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_42);
x_186 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_183);
lean_ctor_set(x_186, 2, x_184);
lean_ctor_set(x_186, 3, x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_134);
x_187 = 0;
lean_ctor_set(x_41, 0, x_186);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_187);
x_188 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; uint8_t x_199; 
x_189 = lean_ctor_get(x_41, 1);
x_190 = lean_ctor_get(x_41, 2);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_41);
x_191 = lean_ctor_get(x_42, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_42, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_42, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_42, 3);
lean_inc(x_194);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_195 = x_42;
} else {
 lean_dec_ref(x_42);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 4, 1);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_191);
lean_ctor_set(x_196, 1, x_192);
lean_ctor_set(x_196, 2, x_193);
lean_ctor_set(x_196, 3, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_134);
x_197 = 0;
x_198 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_189);
lean_ctor_set(x_198, 2, x_190);
lean_ctor_set(x_198, 3, x_123);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_197);
x_199 = 1;
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
}
}
}
}
}
case 1:
{
uint8_t x_200; 
lean_dec(x_35);
lean_dec(x_34);
x_200 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
default: 
{
uint8_t x_201; 
x_201 = l_Std_RBNode_isRed___rarg(x_36);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_36, x_2, x_3);
x_203 = 1;
lean_ctor_set(x_1, 3, x_202);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_203);
return x_1;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_36, x_2, x_3);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_204, 3);
lean_inc(x_206);
if (lean_obj_tag(x_206) == 0)
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_204);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_211; 
x_208 = lean_ctor_get(x_204, 3);
lean_dec(x_208);
x_209 = lean_ctor_get(x_204, 0);
lean_dec(x_209);
x_210 = 0;
lean_ctor_set(x_204, 0, x_206);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_210);
x_211 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_211);
return x_1;
}
else
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; uint8_t x_216; 
x_212 = lean_ctor_get(x_204, 1);
x_213 = lean_ctor_get(x_204, 2);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_204);
x_214 = 0;
x_215 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_215, 0, x_206);
lean_ctor_set(x_215, 1, x_212);
lean_ctor_set(x_215, 2, x_213);
lean_ctor_set(x_215, 3, x_206);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_214);
x_216 = 1;
lean_ctor_set(x_1, 3, x_215);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_216);
return x_1;
}
}
else
{
uint8_t x_217; 
x_217 = lean_ctor_get_uint8(x_206, sizeof(void*)*4);
if (x_217 == 0)
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_204);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_219 = lean_ctor_get(x_204, 1);
x_220 = lean_ctor_get(x_204, 2);
x_221 = lean_ctor_get(x_204, 3);
lean_dec(x_221);
x_222 = lean_ctor_get(x_204, 0);
lean_dec(x_222);
x_223 = !lean_is_exclusive(x_206);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_229; 
x_224 = lean_ctor_get(x_206, 0);
x_225 = lean_ctor_get(x_206, 1);
x_226 = lean_ctor_get(x_206, 2);
x_227 = lean_ctor_get(x_206, 3);
x_228 = 1;
lean_ctor_set(x_206, 3, x_205);
lean_ctor_set(x_206, 2, x_35);
lean_ctor_set(x_206, 1, x_34);
lean_ctor_set(x_206, 0, x_33);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_228);
lean_ctor_set(x_204, 3, x_227);
lean_ctor_set(x_204, 2, x_226);
lean_ctor_set(x_204, 1, x_225);
lean_ctor_set(x_204, 0, x_224);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_228);
x_229 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_229);
return x_1;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; uint8_t x_236; 
x_230 = lean_ctor_get(x_206, 0);
x_231 = lean_ctor_get(x_206, 1);
x_232 = lean_ctor_get(x_206, 2);
x_233 = lean_ctor_get(x_206, 3);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_206);
x_234 = 1;
x_235 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_235, 0, x_33);
lean_ctor_set(x_235, 1, x_34);
lean_ctor_set(x_235, 2, x_35);
lean_ctor_set(x_235, 3, x_205);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_234);
lean_ctor_set(x_204, 3, x_233);
lean_ctor_set(x_204, 2, x_232);
lean_ctor_set(x_204, 1, x_231);
lean_ctor_set(x_204, 0, x_230);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_234);
x_236 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_237 = lean_ctor_get(x_204, 1);
x_238 = lean_ctor_get(x_204, 2);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_204);
x_239 = lean_ctor_get(x_206, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_206, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_206, 2);
lean_inc(x_241);
x_242 = lean_ctor_get(x_206, 3);
lean_inc(x_242);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 lean_ctor_release(x_206, 2);
 lean_ctor_release(x_206, 3);
 x_243 = x_206;
} else {
 lean_dec_ref(x_206);
 x_243 = lean_box(0);
}
x_244 = 1;
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(1, 4, 1);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_33);
lean_ctor_set(x_245, 1, x_34);
lean_ctor_set(x_245, 2, x_35);
lean_ctor_set(x_245, 3, x_205);
lean_ctor_set_uint8(x_245, sizeof(void*)*4, x_244);
x_246 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_246, 0, x_239);
lean_ctor_set(x_246, 1, x_240);
lean_ctor_set(x_246, 2, x_241);
lean_ctor_set(x_246, 3, x_242);
lean_ctor_set_uint8(x_246, sizeof(void*)*4, x_244);
x_247 = 0;
lean_ctor_set(x_1, 3, x_246);
lean_ctor_set(x_1, 2, x_238);
lean_ctor_set(x_1, 1, x_237);
lean_ctor_set(x_1, 0, x_245);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_247);
return x_1;
}
}
else
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_204);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; 
x_249 = lean_ctor_get(x_204, 3);
lean_dec(x_249);
x_250 = lean_ctor_get(x_204, 0);
lean_dec(x_250);
x_251 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_251);
x_252 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_252);
return x_1;
}
else
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; uint8_t x_257; 
x_253 = lean_ctor_get(x_204, 1);
x_254 = lean_ctor_get(x_204, 2);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_204);
x_255 = 0;
x_256 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_256, 0, x_205);
lean_ctor_set(x_256, 1, x_253);
lean_ctor_set(x_256, 2, x_254);
lean_ctor_set(x_256, 3, x_206);
lean_ctor_set_uint8(x_256, sizeof(void*)*4, x_255);
x_257 = 1;
lean_ctor_set(x_1, 3, x_256);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_257);
return x_1;
}
}
}
}
else
{
uint8_t x_258; 
x_258 = lean_ctor_get_uint8(x_205, sizeof(void*)*4);
if (x_258 == 0)
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_204);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_204, 0);
lean_dec(x_260);
x_261 = !lean_is_exclusive(x_205);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_267; 
x_262 = lean_ctor_get(x_205, 0);
x_263 = lean_ctor_get(x_205, 1);
x_264 = lean_ctor_get(x_205, 2);
x_265 = lean_ctor_get(x_205, 3);
x_266 = 1;
lean_ctor_set(x_205, 3, x_262);
lean_ctor_set(x_205, 2, x_35);
lean_ctor_set(x_205, 1, x_34);
lean_ctor_set(x_205, 0, x_33);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_266);
lean_ctor_set(x_204, 0, x_265);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_266);
x_267 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_264);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_205);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_267);
return x_1;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; uint8_t x_274; 
x_268 = lean_ctor_get(x_205, 0);
x_269 = lean_ctor_get(x_205, 1);
x_270 = lean_ctor_get(x_205, 2);
x_271 = lean_ctor_get(x_205, 3);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_205);
x_272 = 1;
x_273 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_273, 0, x_33);
lean_ctor_set(x_273, 1, x_34);
lean_ctor_set(x_273, 2, x_35);
lean_ctor_set(x_273, 3, x_268);
lean_ctor_set_uint8(x_273, sizeof(void*)*4, x_272);
lean_ctor_set(x_204, 0, x_271);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_272);
x_274 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_270);
lean_ctor_set(x_1, 1, x_269);
lean_ctor_set(x_1, 0, x_273);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_274);
return x_1;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_275 = lean_ctor_get(x_204, 1);
x_276 = lean_ctor_get(x_204, 2);
x_277 = lean_ctor_get(x_204, 3);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_204);
x_278 = lean_ctor_get(x_205, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_205, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_205, 2);
lean_inc(x_280);
x_281 = lean_ctor_get(x_205, 3);
lean_inc(x_281);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_282 = x_205;
} else {
 lean_dec_ref(x_205);
 x_282 = lean_box(0);
}
x_283 = 1;
if (lean_is_scalar(x_282)) {
 x_284 = lean_alloc_ctor(1, 4, 1);
} else {
 x_284 = x_282;
}
lean_ctor_set(x_284, 0, x_33);
lean_ctor_set(x_284, 1, x_34);
lean_ctor_set(x_284, 2, x_35);
lean_ctor_set(x_284, 3, x_278);
lean_ctor_set_uint8(x_284, sizeof(void*)*4, x_283);
x_285 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_285, 0, x_281);
lean_ctor_set(x_285, 1, x_275);
lean_ctor_set(x_285, 2, x_276);
lean_ctor_set(x_285, 3, x_277);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_283);
x_286 = 0;
lean_ctor_set(x_1, 3, x_285);
lean_ctor_set(x_1, 2, x_280);
lean_ctor_set(x_1, 1, x_279);
lean_ctor_set(x_1, 0, x_284);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_286);
return x_1;
}
}
else
{
lean_object* x_287; 
x_287 = lean_ctor_get(x_204, 3);
lean_inc(x_287);
if (lean_obj_tag(x_287) == 0)
{
uint8_t x_288; 
x_288 = !lean_is_exclusive(x_204);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; uint8_t x_291; uint8_t x_292; 
x_289 = lean_ctor_get(x_204, 3);
lean_dec(x_289);
x_290 = lean_ctor_get(x_204, 0);
lean_dec(x_290);
x_291 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_291);
x_292 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_292);
return x_1;
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; uint8_t x_297; 
x_293 = lean_ctor_get(x_204, 1);
x_294 = lean_ctor_get(x_204, 2);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_204);
x_295 = 0;
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_205);
lean_ctor_set(x_296, 1, x_293);
lean_ctor_set(x_296, 2, x_294);
lean_ctor_set(x_296, 3, x_287);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_295);
x_297 = 1;
lean_ctor_set(x_1, 3, x_296);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_297);
return x_1;
}
}
else
{
uint8_t x_298; 
x_298 = lean_ctor_get_uint8(x_287, sizeof(void*)*4);
if (x_298 == 0)
{
uint8_t x_299; 
lean_free_object(x_1);
x_299 = !lean_is_exclusive(x_204);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_300 = lean_ctor_get(x_204, 3);
lean_dec(x_300);
x_301 = lean_ctor_get(x_204, 0);
lean_dec(x_301);
x_302 = !lean_is_exclusive(x_287);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; uint8_t x_308; 
x_303 = lean_ctor_get(x_287, 0);
x_304 = lean_ctor_get(x_287, 1);
x_305 = lean_ctor_get(x_287, 2);
x_306 = lean_ctor_get(x_287, 3);
x_307 = 1;
lean_inc(x_205);
lean_ctor_set(x_287, 3, x_205);
lean_ctor_set(x_287, 2, x_35);
lean_ctor_set(x_287, 1, x_34);
lean_ctor_set(x_287, 0, x_33);
x_308 = !lean_is_exclusive(x_205);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_309 = lean_ctor_get(x_205, 3);
lean_dec(x_309);
x_310 = lean_ctor_get(x_205, 2);
lean_dec(x_310);
x_311 = lean_ctor_get(x_205, 1);
lean_dec(x_311);
x_312 = lean_ctor_get(x_205, 0);
lean_dec(x_312);
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_307);
lean_ctor_set(x_205, 3, x_306);
lean_ctor_set(x_205, 2, x_305);
lean_ctor_set(x_205, 1, x_304);
lean_ctor_set(x_205, 0, x_303);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_307);
x_313 = 0;
lean_ctor_set(x_204, 3, x_205);
lean_ctor_set(x_204, 0, x_287);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_313);
return x_204;
}
else
{
lean_object* x_314; uint8_t x_315; 
lean_dec(x_205);
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_307);
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_303);
lean_ctor_set(x_314, 1, x_304);
lean_ctor_set(x_314, 2, x_305);
lean_ctor_set(x_314, 3, x_306);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_307);
x_315 = 0;
lean_ctor_set(x_204, 3, x_314);
lean_ctor_set(x_204, 0, x_287);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_315);
return x_204;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_316 = lean_ctor_get(x_287, 0);
x_317 = lean_ctor_get(x_287, 1);
x_318 = lean_ctor_get(x_287, 2);
x_319 = lean_ctor_get(x_287, 3);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_287);
x_320 = 1;
lean_inc(x_205);
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_33);
lean_ctor_set(x_321, 1, x_34);
lean_ctor_set(x_321, 2, x_35);
lean_ctor_set(x_321, 3, x_205);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_322 = x_205;
} else {
 lean_dec_ref(x_205);
 x_322 = lean_box(0);
}
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_320);
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 4, 1);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_316);
lean_ctor_set(x_323, 1, x_317);
lean_ctor_set(x_323, 2, x_318);
lean_ctor_set(x_323, 3, x_319);
lean_ctor_set_uint8(x_323, sizeof(void*)*4, x_320);
x_324 = 0;
lean_ctor_set(x_204, 3, x_323);
lean_ctor_set(x_204, 0, x_321);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_324);
return x_204;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; 
x_325 = lean_ctor_get(x_204, 1);
x_326 = lean_ctor_get(x_204, 2);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_204);
x_327 = lean_ctor_get(x_287, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_287, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_287, 2);
lean_inc(x_329);
x_330 = lean_ctor_get(x_287, 3);
lean_inc(x_330);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 lean_ctor_release(x_287, 2);
 lean_ctor_release(x_287, 3);
 x_331 = x_287;
} else {
 lean_dec_ref(x_287);
 x_331 = lean_box(0);
}
x_332 = 1;
lean_inc(x_205);
if (lean_is_scalar(x_331)) {
 x_333 = lean_alloc_ctor(1, 4, 1);
} else {
 x_333 = x_331;
}
lean_ctor_set(x_333, 0, x_33);
lean_ctor_set(x_333, 1, x_34);
lean_ctor_set(x_333, 2, x_35);
lean_ctor_set(x_333, 3, x_205);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_334 = x_205;
} else {
 lean_dec_ref(x_205);
 x_334 = lean_box(0);
}
lean_ctor_set_uint8(x_333, sizeof(void*)*4, x_332);
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 4, 1);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_327);
lean_ctor_set(x_335, 1, x_328);
lean_ctor_set(x_335, 2, x_329);
lean_ctor_set(x_335, 3, x_330);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_332);
x_336 = 0;
x_337 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_337, 0, x_333);
lean_ctor_set(x_337, 1, x_325);
lean_ctor_set(x_337, 2, x_326);
lean_ctor_set(x_337, 3, x_335);
lean_ctor_set_uint8(x_337, sizeof(void*)*4, x_336);
return x_337;
}
}
else
{
uint8_t x_338; 
x_338 = !lean_is_exclusive(x_204);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_339 = lean_ctor_get(x_204, 3);
lean_dec(x_339);
x_340 = lean_ctor_get(x_204, 0);
lean_dec(x_340);
x_341 = !lean_is_exclusive(x_205);
if (x_341 == 0)
{
uint8_t x_342; uint8_t x_343; 
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_298);
x_342 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_342);
x_343 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_343);
return x_1;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; uint8_t x_350; 
x_344 = lean_ctor_get(x_205, 0);
x_345 = lean_ctor_get(x_205, 1);
x_346 = lean_ctor_get(x_205, 2);
x_347 = lean_ctor_get(x_205, 3);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_205);
x_348 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_348, 0, x_344);
lean_ctor_set(x_348, 1, x_345);
lean_ctor_set(x_348, 2, x_346);
lean_ctor_set(x_348, 3, x_347);
lean_ctor_set_uint8(x_348, sizeof(void*)*4, x_298);
x_349 = 0;
lean_ctor_set(x_204, 0, x_348);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_349);
x_350 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_350);
return x_1;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; uint8_t x_361; 
x_351 = lean_ctor_get(x_204, 1);
x_352 = lean_ctor_get(x_204, 2);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_204);
x_353 = lean_ctor_get(x_205, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_205, 1);
lean_inc(x_354);
x_355 = lean_ctor_get(x_205, 2);
lean_inc(x_355);
x_356 = lean_ctor_get(x_205, 3);
lean_inc(x_356);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_357 = x_205;
} else {
 lean_dec_ref(x_205);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 4, 1);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_353);
lean_ctor_set(x_358, 1, x_354);
lean_ctor_set(x_358, 2, x_355);
lean_ctor_set(x_358, 3, x_356);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_298);
x_359 = 0;
x_360 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_351);
lean_ctor_set(x_360, 2, x_352);
lean_ctor_set(x_360, 3, x_287);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
x_361 = 1;
lean_ctor_set(x_1, 3, x_360);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_361);
return x_1;
}
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
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_362 = lean_ctor_get(x_1, 0);
x_363 = lean_ctor_get(x_1, 1);
x_364 = lean_ctor_get(x_1, 2);
x_365 = lean_ctor_get(x_1, 3);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_1);
x_366 = l_Lean_Name_quickCmp(x_2, x_363);
switch (x_366) {
case 0:
{
uint8_t x_367; 
x_367 = l_Std_RBNode_isRed___rarg(x_362);
if (x_367 == 0)
{
lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_368 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_362, x_2, x_3);
x_369 = 1;
x_370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_363);
lean_ctor_set(x_370, 2, x_364);
lean_ctor_set(x_370, 3, x_365);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_369);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; 
x_371 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_362, x_2, x_3);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; 
x_373 = lean_ctor_get(x_371, 3);
lean_inc(x_373);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; 
x_374 = lean_ctor_get(x_371, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_371, 2);
lean_inc(x_375);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_376 = x_371;
} else {
 lean_dec_ref(x_371);
 x_376 = lean_box(0);
}
x_377 = 0;
if (lean_is_scalar(x_376)) {
 x_378 = lean_alloc_ctor(1, 4, 1);
} else {
 x_378 = x_376;
}
lean_ctor_set(x_378, 0, x_373);
lean_ctor_set(x_378, 1, x_374);
lean_ctor_set(x_378, 2, x_375);
lean_ctor_set(x_378, 3, x_373);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_377);
x_379 = 1;
x_380 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_363);
lean_ctor_set(x_380, 2, x_364);
lean_ctor_set(x_380, 3, x_365);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_379);
return x_380;
}
else
{
uint8_t x_381; 
x_381 = lean_ctor_get_uint8(x_373, sizeof(void*)*4);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; 
x_382 = lean_ctor_get(x_371, 1);
lean_inc(x_382);
x_383 = lean_ctor_get(x_371, 2);
lean_inc(x_383);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_384 = x_371;
} else {
 lean_dec_ref(x_371);
 x_384 = lean_box(0);
}
x_385 = lean_ctor_get(x_373, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_373, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_373, 2);
lean_inc(x_387);
x_388 = lean_ctor_get(x_373, 3);
lean_inc(x_388);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 lean_ctor_release(x_373, 2);
 lean_ctor_release(x_373, 3);
 x_389 = x_373;
} else {
 lean_dec_ref(x_373);
 x_389 = lean_box(0);
}
x_390 = 1;
if (lean_is_scalar(x_389)) {
 x_391 = lean_alloc_ctor(1, 4, 1);
} else {
 x_391 = x_389;
}
lean_ctor_set(x_391, 0, x_372);
lean_ctor_set(x_391, 1, x_382);
lean_ctor_set(x_391, 2, x_383);
lean_ctor_set(x_391, 3, x_385);
lean_ctor_set_uint8(x_391, sizeof(void*)*4, x_390);
if (lean_is_scalar(x_384)) {
 x_392 = lean_alloc_ctor(1, 4, 1);
} else {
 x_392 = x_384;
}
lean_ctor_set(x_392, 0, x_388);
lean_ctor_set(x_392, 1, x_363);
lean_ctor_set(x_392, 2, x_364);
lean_ctor_set(x_392, 3, x_365);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_390);
x_393 = 0;
x_394 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_386);
lean_ctor_set(x_394, 2, x_387);
lean_ctor_set(x_394, 3, x_392);
lean_ctor_set_uint8(x_394, sizeof(void*)*4, x_393);
return x_394;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; 
x_395 = lean_ctor_get(x_371, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_371, 2);
lean_inc(x_396);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_397 = x_371;
} else {
 lean_dec_ref(x_371);
 x_397 = lean_box(0);
}
x_398 = 0;
if (lean_is_scalar(x_397)) {
 x_399 = lean_alloc_ctor(1, 4, 1);
} else {
 x_399 = x_397;
}
lean_ctor_set(x_399, 0, x_372);
lean_ctor_set(x_399, 1, x_395);
lean_ctor_set(x_399, 2, x_396);
lean_ctor_set(x_399, 3, x_373);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_398);
x_400 = 1;
x_401 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_363);
lean_ctor_set(x_401, 2, x_364);
lean_ctor_set(x_401, 3, x_365);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_400);
return x_401;
}
}
}
else
{
uint8_t x_402; 
x_402 = lean_ctor_get_uint8(x_372, sizeof(void*)*4);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; lean_object* x_416; 
x_403 = lean_ctor_get(x_371, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_371, 2);
lean_inc(x_404);
x_405 = lean_ctor_get(x_371, 3);
lean_inc(x_405);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_406 = x_371;
} else {
 lean_dec_ref(x_371);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_372, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_372, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_372, 2);
lean_inc(x_409);
x_410 = lean_ctor_get(x_372, 3);
lean_inc(x_410);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_411 = x_372;
} else {
 lean_dec_ref(x_372);
 x_411 = lean_box(0);
}
x_412 = 1;
if (lean_is_scalar(x_411)) {
 x_413 = lean_alloc_ctor(1, 4, 1);
} else {
 x_413 = x_411;
}
lean_ctor_set(x_413, 0, x_407);
lean_ctor_set(x_413, 1, x_408);
lean_ctor_set(x_413, 2, x_409);
lean_ctor_set(x_413, 3, x_410);
lean_ctor_set_uint8(x_413, sizeof(void*)*4, x_412);
if (lean_is_scalar(x_406)) {
 x_414 = lean_alloc_ctor(1, 4, 1);
} else {
 x_414 = x_406;
}
lean_ctor_set(x_414, 0, x_405);
lean_ctor_set(x_414, 1, x_363);
lean_ctor_set(x_414, 2, x_364);
lean_ctor_set(x_414, 3, x_365);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_412);
x_415 = 0;
x_416 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_416, 0, x_413);
lean_ctor_set(x_416, 1, x_403);
lean_ctor_set(x_416, 2, x_404);
lean_ctor_set(x_416, 3, x_414);
lean_ctor_set_uint8(x_416, sizeof(void*)*4, x_415);
return x_416;
}
else
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_371, 3);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; uint8_t x_423; lean_object* x_424; 
x_418 = lean_ctor_get(x_371, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_371, 2);
lean_inc(x_419);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_420 = x_371;
} else {
 lean_dec_ref(x_371);
 x_420 = lean_box(0);
}
x_421 = 0;
if (lean_is_scalar(x_420)) {
 x_422 = lean_alloc_ctor(1, 4, 1);
} else {
 x_422 = x_420;
}
lean_ctor_set(x_422, 0, x_372);
lean_ctor_set(x_422, 1, x_418);
lean_ctor_set(x_422, 2, x_419);
lean_ctor_set(x_422, 3, x_417);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
x_423 = 1;
x_424 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_363);
lean_ctor_set(x_424, 2, x_364);
lean_ctor_set(x_424, 3, x_365);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_423);
return x_424;
}
else
{
uint8_t x_425; 
x_425 = lean_ctor_get_uint8(x_417, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; 
x_426 = lean_ctor_get(x_371, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_371, 2);
lean_inc(x_427);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_428 = x_371;
} else {
 lean_dec_ref(x_371);
 x_428 = lean_box(0);
}
x_429 = lean_ctor_get(x_417, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_417, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_417, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_417, 3);
lean_inc(x_432);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_433 = x_417;
} else {
 lean_dec_ref(x_417);
 x_433 = lean_box(0);
}
x_434 = 1;
lean_inc(x_372);
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(1, 4, 1);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_372);
lean_ctor_set(x_435, 1, x_426);
lean_ctor_set(x_435, 2, x_427);
lean_ctor_set(x_435, 3, x_429);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_436 = x_372;
} else {
 lean_dec_ref(x_372);
 x_436 = lean_box(0);
}
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_434);
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 4, 1);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_432);
lean_ctor_set(x_437, 1, x_363);
lean_ctor_set(x_437, 2, x_364);
lean_ctor_set(x_437, 3, x_365);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_434);
x_438 = 0;
if (lean_is_scalar(x_428)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_428;
}
lean_ctor_set(x_439, 0, x_435);
lean_ctor_set(x_439, 1, x_430);
lean_ctor_set(x_439, 2, x_431);
lean_ctor_set(x_439, 3, x_437);
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
return x_439;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; 
x_440 = lean_ctor_get(x_371, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_371, 2);
lean_inc(x_441);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_442 = x_371;
} else {
 lean_dec_ref(x_371);
 x_442 = lean_box(0);
}
x_443 = lean_ctor_get(x_372, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_372, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_372, 2);
lean_inc(x_445);
x_446 = lean_ctor_get(x_372, 3);
lean_inc(x_446);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_447 = x_372;
} else {
 lean_dec_ref(x_372);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 4, 1);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_443);
lean_ctor_set(x_448, 1, x_444);
lean_ctor_set(x_448, 2, x_445);
lean_ctor_set(x_448, 3, x_446);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_425);
x_449 = 0;
if (lean_is_scalar(x_442)) {
 x_450 = lean_alloc_ctor(1, 4, 1);
} else {
 x_450 = x_442;
}
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_440);
lean_ctor_set(x_450, 2, x_441);
lean_ctor_set(x_450, 3, x_417);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
x_451 = 1;
x_452 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_452, 0, x_450);
lean_ctor_set(x_452, 1, x_363);
lean_ctor_set(x_452, 2, x_364);
lean_ctor_set(x_452, 3, x_365);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_451);
return x_452;
}
}
}
}
}
}
case 1:
{
uint8_t x_453; lean_object* x_454; 
lean_dec(x_364);
lean_dec(x_363);
x_453 = 1;
x_454 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_454, 0, x_362);
lean_ctor_set(x_454, 1, x_2);
lean_ctor_set(x_454, 2, x_3);
lean_ctor_set(x_454, 3, x_365);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_453);
return x_454;
}
default: 
{
uint8_t x_455; 
x_455 = l_Std_RBNode_isRed___rarg(x_365);
if (x_455 == 0)
{
lean_object* x_456; uint8_t x_457; lean_object* x_458; 
x_456 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_365, x_2, x_3);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_362);
lean_ctor_set(x_458, 1, x_363);
lean_ctor_set(x_458, 2, x_364);
lean_ctor_set(x_458, 3, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
else
{
lean_object* x_459; lean_object* x_460; 
x_459 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_365, x_2, x_3);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; 
x_461 = lean_ctor_get(x_459, 3);
lean_inc(x_461);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; 
x_462 = lean_ctor_get(x_459, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_459, 2);
lean_inc(x_463);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_464 = x_459;
} else {
 lean_dec_ref(x_459);
 x_464 = lean_box(0);
}
x_465 = 0;
if (lean_is_scalar(x_464)) {
 x_466 = lean_alloc_ctor(1, 4, 1);
} else {
 x_466 = x_464;
}
lean_ctor_set(x_466, 0, x_461);
lean_ctor_set(x_466, 1, x_462);
lean_ctor_set(x_466, 2, x_463);
lean_ctor_set(x_466, 3, x_461);
lean_ctor_set_uint8(x_466, sizeof(void*)*4, x_465);
x_467 = 1;
x_468 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_468, 0, x_362);
lean_ctor_set(x_468, 1, x_363);
lean_ctor_set(x_468, 2, x_364);
lean_ctor_set(x_468, 3, x_466);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_467);
return x_468;
}
else
{
uint8_t x_469; 
x_469 = lean_ctor_get_uint8(x_461, sizeof(void*)*4);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; uint8_t x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; lean_object* x_482; 
x_470 = lean_ctor_get(x_459, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_459, 2);
lean_inc(x_471);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_472 = x_459;
} else {
 lean_dec_ref(x_459);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_461, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_461, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_461, 2);
lean_inc(x_475);
x_476 = lean_ctor_get(x_461, 3);
lean_inc(x_476);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 lean_ctor_release(x_461, 2);
 lean_ctor_release(x_461, 3);
 x_477 = x_461;
} else {
 lean_dec_ref(x_461);
 x_477 = lean_box(0);
}
x_478 = 1;
if (lean_is_scalar(x_477)) {
 x_479 = lean_alloc_ctor(1, 4, 1);
} else {
 x_479 = x_477;
}
lean_ctor_set(x_479, 0, x_362);
lean_ctor_set(x_479, 1, x_363);
lean_ctor_set(x_479, 2, x_364);
lean_ctor_set(x_479, 3, x_460);
lean_ctor_set_uint8(x_479, sizeof(void*)*4, x_478);
if (lean_is_scalar(x_472)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_472;
}
lean_ctor_set(x_480, 0, x_473);
lean_ctor_set(x_480, 1, x_474);
lean_ctor_set(x_480, 2, x_475);
lean_ctor_set(x_480, 3, x_476);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_478);
x_481 = 0;
x_482 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_482, 0, x_479);
lean_ctor_set(x_482, 1, x_470);
lean_ctor_set(x_482, 2, x_471);
lean_ctor_set(x_482, 3, x_480);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_481);
return x_482;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; 
x_483 = lean_ctor_get(x_459, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_459, 2);
lean_inc(x_484);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_485 = x_459;
} else {
 lean_dec_ref(x_459);
 x_485 = lean_box(0);
}
x_486 = 0;
if (lean_is_scalar(x_485)) {
 x_487 = lean_alloc_ctor(1, 4, 1);
} else {
 x_487 = x_485;
}
lean_ctor_set(x_487, 0, x_460);
lean_ctor_set(x_487, 1, x_483);
lean_ctor_set(x_487, 2, x_484);
lean_ctor_set(x_487, 3, x_461);
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_486);
x_488 = 1;
x_489 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_489, 0, x_362);
lean_ctor_set(x_489, 1, x_363);
lean_ctor_set(x_489, 2, x_364);
lean_ctor_set(x_489, 3, x_487);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_488);
return x_489;
}
}
}
else
{
uint8_t x_490; 
x_490 = lean_ctor_get_uint8(x_460, sizeof(void*)*4);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; lean_object* x_504; 
x_491 = lean_ctor_get(x_459, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_459, 2);
lean_inc(x_492);
x_493 = lean_ctor_get(x_459, 3);
lean_inc(x_493);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_494 = x_459;
} else {
 lean_dec_ref(x_459);
 x_494 = lean_box(0);
}
x_495 = lean_ctor_get(x_460, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_460, 1);
lean_inc(x_496);
x_497 = lean_ctor_get(x_460, 2);
lean_inc(x_497);
x_498 = lean_ctor_get(x_460, 3);
lean_inc(x_498);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_499 = x_460;
} else {
 lean_dec_ref(x_460);
 x_499 = lean_box(0);
}
x_500 = 1;
if (lean_is_scalar(x_499)) {
 x_501 = lean_alloc_ctor(1, 4, 1);
} else {
 x_501 = x_499;
}
lean_ctor_set(x_501, 0, x_362);
lean_ctor_set(x_501, 1, x_363);
lean_ctor_set(x_501, 2, x_364);
lean_ctor_set(x_501, 3, x_495);
lean_ctor_set_uint8(x_501, sizeof(void*)*4, x_500);
if (lean_is_scalar(x_494)) {
 x_502 = lean_alloc_ctor(1, 4, 1);
} else {
 x_502 = x_494;
}
lean_ctor_set(x_502, 0, x_498);
lean_ctor_set(x_502, 1, x_491);
lean_ctor_set(x_502, 2, x_492);
lean_ctor_set(x_502, 3, x_493);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_500);
x_503 = 0;
x_504 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_496);
lean_ctor_set(x_504, 2, x_497);
lean_ctor_set(x_504, 3, x_502);
lean_ctor_set_uint8(x_504, sizeof(void*)*4, x_503);
return x_504;
}
else
{
lean_object* x_505; 
x_505 = lean_ctor_get(x_459, 3);
lean_inc(x_505);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; uint8_t x_511; lean_object* x_512; 
x_506 = lean_ctor_get(x_459, 1);
lean_inc(x_506);
x_507 = lean_ctor_get(x_459, 2);
lean_inc(x_507);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_508 = x_459;
} else {
 lean_dec_ref(x_459);
 x_508 = lean_box(0);
}
x_509 = 0;
if (lean_is_scalar(x_508)) {
 x_510 = lean_alloc_ctor(1, 4, 1);
} else {
 x_510 = x_508;
}
lean_ctor_set(x_510, 0, x_460);
lean_ctor_set(x_510, 1, x_506);
lean_ctor_set(x_510, 2, x_507);
lean_ctor_set(x_510, 3, x_505);
lean_ctor_set_uint8(x_510, sizeof(void*)*4, x_509);
x_511 = 1;
x_512 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_512, 0, x_362);
lean_ctor_set(x_512, 1, x_363);
lean_ctor_set(x_512, 2, x_364);
lean_ctor_set(x_512, 3, x_510);
lean_ctor_set_uint8(x_512, sizeof(void*)*4, x_511);
return x_512;
}
else
{
uint8_t x_513; 
x_513 = lean_ctor_get_uint8(x_505, sizeof(void*)*4);
if (x_513 == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; 
x_514 = lean_ctor_get(x_459, 1);
lean_inc(x_514);
x_515 = lean_ctor_get(x_459, 2);
lean_inc(x_515);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_516 = x_459;
} else {
 lean_dec_ref(x_459);
 x_516 = lean_box(0);
}
x_517 = lean_ctor_get(x_505, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_505, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_505, 2);
lean_inc(x_519);
x_520 = lean_ctor_get(x_505, 3);
lean_inc(x_520);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 lean_ctor_release(x_505, 2);
 lean_ctor_release(x_505, 3);
 x_521 = x_505;
} else {
 lean_dec_ref(x_505);
 x_521 = lean_box(0);
}
x_522 = 1;
lean_inc(x_460);
if (lean_is_scalar(x_521)) {
 x_523 = lean_alloc_ctor(1, 4, 1);
} else {
 x_523 = x_521;
}
lean_ctor_set(x_523, 0, x_362);
lean_ctor_set(x_523, 1, x_363);
lean_ctor_set(x_523, 2, x_364);
lean_ctor_set(x_523, 3, x_460);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_524 = x_460;
} else {
 lean_dec_ref(x_460);
 x_524 = lean_box(0);
}
lean_ctor_set_uint8(x_523, sizeof(void*)*4, x_522);
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(1, 4, 1);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_517);
lean_ctor_set(x_525, 1, x_518);
lean_ctor_set(x_525, 2, x_519);
lean_ctor_set(x_525, 3, x_520);
lean_ctor_set_uint8(x_525, sizeof(void*)*4, x_522);
x_526 = 0;
if (lean_is_scalar(x_516)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_516;
}
lean_ctor_set(x_527, 0, x_523);
lean_ctor_set(x_527, 1, x_514);
lean_ctor_set(x_527, 2, x_515);
lean_ctor_set(x_527, 3, x_525);
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
return x_527;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; uint8_t x_537; lean_object* x_538; uint8_t x_539; lean_object* x_540; 
x_528 = lean_ctor_get(x_459, 1);
lean_inc(x_528);
x_529 = lean_ctor_get(x_459, 2);
lean_inc(x_529);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_530 = x_459;
} else {
 lean_dec_ref(x_459);
 x_530 = lean_box(0);
}
x_531 = lean_ctor_get(x_460, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_460, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_460, 2);
lean_inc(x_533);
x_534 = lean_ctor_get(x_460, 3);
lean_inc(x_534);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_535 = x_460;
} else {
 lean_dec_ref(x_460);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 4, 1);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_531);
lean_ctor_set(x_536, 1, x_532);
lean_ctor_set(x_536, 2, x_533);
lean_ctor_set(x_536, 3, x_534);
lean_ctor_set_uint8(x_536, sizeof(void*)*4, x_513);
x_537 = 0;
if (lean_is_scalar(x_530)) {
 x_538 = lean_alloc_ctor(1, 4, 1);
} else {
 x_538 = x_530;
}
lean_ctor_set(x_538, 0, x_536);
lean_ctor_set(x_538, 1, x_528);
lean_ctor_set(x_538, 2, x_529);
lean_ctor_set(x_538, 3, x_505);
lean_ctor_set_uint8(x_538, sizeof(void*)*4, x_537);
x_539 = 1;
x_540 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_540, 0, x_362);
lean_ctor_set(x_540, 1, x_363);
lean_ctor_set(x_540, 2, x_364);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_539);
return x_540;
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
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_13 = l_Lean_Name_quickCmp(x_2, x_10);
switch (x_13) {
case 0:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_9, x_2, x_3);
x_15 = 0;
lean_ctor_set(x_1, 0, x_14);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
case 1:
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
default: 
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_12, x_2, x_3);
x_18 = 0;
lean_ctor_set(x_1, 3, x_17);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_18);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_23 = l_Lean_Name_quickCmp(x_2, x_20);
switch (x_23) {
case 0:
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_19, x_2, x_3);
x_25 = 0;
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_25);
return x_26;
}
case 1:
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
default: 
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_22, x_2, x_3);
x_30 = 0;
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 2);
x_36 = lean_ctor_get(x_1, 3);
x_37 = l_Lean_Name_quickCmp(x_2, x_34);
switch (x_37) {
case 0:
{
uint8_t x_38; 
x_38 = l_Std_RBNode_isRed___rarg(x_33);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_33, x_2, x_3);
x_40 = 1;
lean_ctor_set(x_1, 0, x_39);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_40);
return x_1;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_33, x_2, x_3);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 3);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_41, 3);
lean_dec(x_45);
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = 0;
lean_ctor_set(x_41, 0, x_43);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_47);
x_48 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_41, 1);
x_50 = lean_ctor_get(x_41, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = 0;
x_52 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 2, x_50);
lean_ctor_set(x_52, 3, x_43);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_51);
x_53 = 1;
lean_ctor_set(x_1, 0, x_52);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_53);
return x_1;
}
}
else
{
uint8_t x_54; 
x_54 = lean_ctor_get_uint8(x_43, sizeof(void*)*4);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_41);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_41, 1);
x_57 = lean_ctor_get(x_41, 2);
x_58 = lean_ctor_get(x_41, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_41, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_43);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_43, 0);
x_62 = lean_ctor_get(x_43, 1);
x_63 = lean_ctor_get(x_43, 2);
x_64 = lean_ctor_get(x_43, 3);
x_65 = 1;
lean_ctor_set(x_43, 3, x_61);
lean_ctor_set(x_43, 2, x_57);
lean_ctor_set(x_43, 1, x_56);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_65);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_64);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_65);
x_66 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_63);
lean_ctor_set(x_1, 1, x_62);
lean_ctor_set(x_1, 0, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; 
x_67 = lean_ctor_get(x_43, 0);
x_68 = lean_ctor_get(x_43, 1);
x_69 = lean_ctor_get(x_43, 2);
x_70 = lean_ctor_get(x_43, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_43);
x_71 = 1;
x_72 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_72, 0, x_42);
lean_ctor_set(x_72, 1, x_56);
lean_ctor_set(x_72, 2, x_57);
lean_ctor_set(x_72, 3, x_67);
lean_ctor_set_uint8(x_72, sizeof(void*)*4, x_71);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_70);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_71);
x_73 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_69);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_72);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_73);
return x_1;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_74 = lean_ctor_get(x_41, 1);
x_75 = lean_ctor_get(x_41, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_41);
x_76 = lean_ctor_get(x_43, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_43, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_43, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_43, 3);
lean_inc(x_79);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_80 = x_43;
} else {
 lean_dec_ref(x_43);
 x_80 = lean_box(0);
}
x_81 = 1;
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(1, 4, 1);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_42);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_75);
lean_ctor_set(x_82, 3, x_76);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_81);
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_34);
lean_ctor_set(x_83, 2, x_35);
lean_ctor_set(x_83, 3, x_36);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_81);
x_84 = 0;
lean_ctor_set(x_1, 3, x_83);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_82);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_84);
return x_1;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_41);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_41, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_41, 0);
lean_dec(x_87);
x_88 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_88);
x_89 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_89);
return x_1;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_41, 1);
x_91 = lean_ctor_get(x_41, 2);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_41);
x_92 = 0;
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_42);
lean_ctor_set(x_93, 1, x_90);
lean_ctor_set(x_93, 2, x_91);
lean_ctor_set(x_93, 3, x_43);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_92);
x_94 = 1;
lean_ctor_set(x_1, 0, x_93);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_94);
return x_1;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_42, sizeof(void*)*4);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_41);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_41, 1);
x_98 = lean_ctor_get(x_41, 2);
x_99 = lean_ctor_get(x_41, 3);
x_100 = lean_ctor_get(x_41, 0);
lean_dec(x_100);
x_101 = !lean_is_exclusive(x_42);
if (x_101 == 0)
{
uint8_t x_102; uint8_t x_103; 
x_102 = 1;
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_102);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_102);
x_103 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_42);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_103);
return x_1;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; uint8_t x_110; 
x_104 = lean_ctor_get(x_42, 0);
x_105 = lean_ctor_get(x_42, 1);
x_106 = lean_ctor_get(x_42, 2);
x_107 = lean_ctor_get(x_42, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_42);
x_108 = 1;
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_105);
lean_ctor_set(x_109, 2, x_106);
lean_ctor_set(x_109, 3, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_108);
x_110 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_110);
return x_1;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_111 = lean_ctor_get(x_41, 1);
x_112 = lean_ctor_get(x_41, 2);
x_113 = lean_ctor_get(x_41, 3);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_41);
x_114 = lean_ctor_get(x_42, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_42, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_42, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_42, 3);
lean_inc(x_117);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_118 = x_42;
} else {
 lean_dec_ref(x_42);
 x_118 = lean_box(0);
}
x_119 = 1;
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(1, 4, 1);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_114);
lean_ctor_set(x_120, 1, x_115);
lean_ctor_set(x_120, 2, x_116);
lean_ctor_set(x_120, 3, x_117);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_119);
x_121 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_121, 0, x_113);
lean_ctor_set(x_121, 1, x_34);
lean_ctor_set(x_121, 2, x_35);
lean_ctor_set(x_121, 3, x_36);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_119);
x_122 = 0;
lean_ctor_set(x_1, 3, x_121);
lean_ctor_set(x_1, 2, x_112);
lean_ctor_set(x_1, 1, x_111);
lean_ctor_set(x_1, 0, x_120);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_122);
return x_1;
}
}
else
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_41, 3);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_41);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_41, 3);
lean_dec(x_125);
x_126 = lean_ctor_get(x_41, 0);
lean_dec(x_126);
x_127 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_127);
x_128 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_128);
return x_1;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_41, 1);
x_130 = lean_ctor_get(x_41, 2);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_41);
x_131 = 0;
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_42);
lean_ctor_set(x_132, 1, x_129);
lean_ctor_set(x_132, 2, x_130);
lean_ctor_set(x_132, 3, x_123);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_131);
x_133 = 1;
lean_ctor_set(x_1, 0, x_132);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_133);
return x_1;
}
}
else
{
uint8_t x_134; 
x_134 = lean_ctor_get_uint8(x_123, sizeof(void*)*4);
if (x_134 == 0)
{
uint8_t x_135; 
lean_free_object(x_1);
x_135 = !lean_is_exclusive(x_41);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_41, 1);
x_137 = lean_ctor_get(x_41, 2);
x_138 = lean_ctor_get(x_41, 3);
lean_dec(x_138);
x_139 = lean_ctor_get(x_41, 0);
lean_dec(x_139);
x_140 = !lean_is_exclusive(x_123);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; 
x_141 = lean_ctor_get(x_123, 0);
x_142 = lean_ctor_get(x_123, 1);
x_143 = lean_ctor_get(x_123, 2);
x_144 = lean_ctor_get(x_123, 3);
x_145 = 1;
lean_inc(x_42);
lean_ctor_set(x_123, 3, x_141);
lean_ctor_set(x_123, 2, x_137);
lean_ctor_set(x_123, 1, x_136);
lean_ctor_set(x_123, 0, x_42);
x_146 = !lean_is_exclusive(x_42);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_147 = lean_ctor_get(x_42, 3);
lean_dec(x_147);
x_148 = lean_ctor_get(x_42, 2);
lean_dec(x_148);
x_149 = lean_ctor_get(x_42, 1);
lean_dec(x_149);
x_150 = lean_ctor_get(x_42, 0);
lean_dec(x_150);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_145);
lean_ctor_set(x_42, 3, x_36);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 0, x_144);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_145);
x_151 = 0;
lean_ctor_set(x_41, 3, x_42);
lean_ctor_set(x_41, 2, x_143);
lean_ctor_set(x_41, 1, x_142);
lean_ctor_set(x_41, 0, x_123);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_151);
return x_41;
}
else
{
lean_object* x_152; uint8_t x_153; 
lean_dec(x_42);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_145);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_34);
lean_ctor_set(x_152, 2, x_35);
lean_ctor_set(x_152, 3, x_36);
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_145);
x_153 = 0;
lean_ctor_set(x_41, 3, x_152);
lean_ctor_set(x_41, 2, x_143);
lean_ctor_set(x_41, 1, x_142);
lean_ctor_set(x_41, 0, x_123);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_153);
return x_41;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_154 = lean_ctor_get(x_123, 0);
x_155 = lean_ctor_get(x_123, 1);
x_156 = lean_ctor_get(x_123, 2);
x_157 = lean_ctor_get(x_123, 3);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_123);
x_158 = 1;
lean_inc(x_42);
x_159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_159, 0, x_42);
lean_ctor_set(x_159, 1, x_136);
lean_ctor_set(x_159, 2, x_137);
lean_ctor_set(x_159, 3, x_154);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_160 = x_42;
} else {
 lean_dec_ref(x_42);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_158);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_157);
lean_ctor_set(x_161, 1, x_34);
lean_ctor_set(x_161, 2, x_35);
lean_ctor_set(x_161, 3, x_36);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_158);
x_162 = 0;
lean_ctor_set(x_41, 3, x_161);
lean_ctor_set(x_41, 2, x_156);
lean_ctor_set(x_41, 1, x_155);
lean_ctor_set(x_41, 0, x_159);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_162);
return x_41;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; 
x_163 = lean_ctor_get(x_41, 1);
x_164 = lean_ctor_get(x_41, 2);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_41);
x_165 = lean_ctor_get(x_123, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_123, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_123, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_123, 3);
lean_inc(x_168);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 x_169 = x_123;
} else {
 lean_dec_ref(x_123);
 x_169 = lean_box(0);
}
x_170 = 1;
lean_inc(x_42);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(1, 4, 1);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_42);
lean_ctor_set(x_171, 1, x_163);
lean_ctor_set(x_171, 2, x_164);
lean_ctor_set(x_171, 3, x_165);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_172 = x_42;
} else {
 lean_dec_ref(x_42);
 x_172 = lean_box(0);
}
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_170);
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 4, 1);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_34);
lean_ctor_set(x_173, 2, x_35);
lean_ctor_set(x_173, 3, x_36);
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_170);
x_174 = 0;
x_175 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_166);
lean_ctor_set(x_175, 2, x_167);
lean_ctor_set(x_175, 3, x_173);
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_174);
return x_175;
}
}
else
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_41);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = lean_ctor_get(x_41, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_41, 0);
lean_dec(x_178);
x_179 = !lean_is_exclusive(x_42);
if (x_179 == 0)
{
uint8_t x_180; uint8_t x_181; 
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_134);
x_180 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_180);
x_181 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_181);
return x_1;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_188; 
x_182 = lean_ctor_get(x_42, 0);
x_183 = lean_ctor_get(x_42, 1);
x_184 = lean_ctor_get(x_42, 2);
x_185 = lean_ctor_get(x_42, 3);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_42);
x_186 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_183);
lean_ctor_set(x_186, 2, x_184);
lean_ctor_set(x_186, 3, x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_134);
x_187 = 0;
lean_ctor_set(x_41, 0, x_186);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_187);
x_188 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; uint8_t x_199; 
x_189 = lean_ctor_get(x_41, 1);
x_190 = lean_ctor_get(x_41, 2);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_41);
x_191 = lean_ctor_get(x_42, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_42, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_42, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_42, 3);
lean_inc(x_194);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_195 = x_42;
} else {
 lean_dec_ref(x_42);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 4, 1);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_191);
lean_ctor_set(x_196, 1, x_192);
lean_ctor_set(x_196, 2, x_193);
lean_ctor_set(x_196, 3, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_134);
x_197 = 0;
x_198 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_189);
lean_ctor_set(x_198, 2, x_190);
lean_ctor_set(x_198, 3, x_123);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_197);
x_199 = 1;
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
}
}
}
}
}
case 1:
{
uint8_t x_200; 
lean_dec(x_35);
lean_dec(x_34);
x_200 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
default: 
{
uint8_t x_201; 
x_201 = l_Std_RBNode_isRed___rarg(x_36);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_36, x_2, x_3);
x_203 = 1;
lean_ctor_set(x_1, 3, x_202);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_203);
return x_1;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_36, x_2, x_3);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_204, 3);
lean_inc(x_206);
if (lean_obj_tag(x_206) == 0)
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_204);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_211; 
x_208 = lean_ctor_get(x_204, 3);
lean_dec(x_208);
x_209 = lean_ctor_get(x_204, 0);
lean_dec(x_209);
x_210 = 0;
lean_ctor_set(x_204, 0, x_206);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_210);
x_211 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_211);
return x_1;
}
else
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; uint8_t x_216; 
x_212 = lean_ctor_get(x_204, 1);
x_213 = lean_ctor_get(x_204, 2);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_204);
x_214 = 0;
x_215 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_215, 0, x_206);
lean_ctor_set(x_215, 1, x_212);
lean_ctor_set(x_215, 2, x_213);
lean_ctor_set(x_215, 3, x_206);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_214);
x_216 = 1;
lean_ctor_set(x_1, 3, x_215);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_216);
return x_1;
}
}
else
{
uint8_t x_217; 
x_217 = lean_ctor_get_uint8(x_206, sizeof(void*)*4);
if (x_217 == 0)
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_204);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_219 = lean_ctor_get(x_204, 1);
x_220 = lean_ctor_get(x_204, 2);
x_221 = lean_ctor_get(x_204, 3);
lean_dec(x_221);
x_222 = lean_ctor_get(x_204, 0);
lean_dec(x_222);
x_223 = !lean_is_exclusive(x_206);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_229; 
x_224 = lean_ctor_get(x_206, 0);
x_225 = lean_ctor_get(x_206, 1);
x_226 = lean_ctor_get(x_206, 2);
x_227 = lean_ctor_get(x_206, 3);
x_228 = 1;
lean_ctor_set(x_206, 3, x_205);
lean_ctor_set(x_206, 2, x_35);
lean_ctor_set(x_206, 1, x_34);
lean_ctor_set(x_206, 0, x_33);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_228);
lean_ctor_set(x_204, 3, x_227);
lean_ctor_set(x_204, 2, x_226);
lean_ctor_set(x_204, 1, x_225);
lean_ctor_set(x_204, 0, x_224);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_228);
x_229 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_229);
return x_1;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; uint8_t x_236; 
x_230 = lean_ctor_get(x_206, 0);
x_231 = lean_ctor_get(x_206, 1);
x_232 = lean_ctor_get(x_206, 2);
x_233 = lean_ctor_get(x_206, 3);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_206);
x_234 = 1;
x_235 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_235, 0, x_33);
lean_ctor_set(x_235, 1, x_34);
lean_ctor_set(x_235, 2, x_35);
lean_ctor_set(x_235, 3, x_205);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_234);
lean_ctor_set(x_204, 3, x_233);
lean_ctor_set(x_204, 2, x_232);
lean_ctor_set(x_204, 1, x_231);
lean_ctor_set(x_204, 0, x_230);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_234);
x_236 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_237 = lean_ctor_get(x_204, 1);
x_238 = lean_ctor_get(x_204, 2);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_204);
x_239 = lean_ctor_get(x_206, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_206, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_206, 2);
lean_inc(x_241);
x_242 = lean_ctor_get(x_206, 3);
lean_inc(x_242);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 lean_ctor_release(x_206, 2);
 lean_ctor_release(x_206, 3);
 x_243 = x_206;
} else {
 lean_dec_ref(x_206);
 x_243 = lean_box(0);
}
x_244 = 1;
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(1, 4, 1);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_33);
lean_ctor_set(x_245, 1, x_34);
lean_ctor_set(x_245, 2, x_35);
lean_ctor_set(x_245, 3, x_205);
lean_ctor_set_uint8(x_245, sizeof(void*)*4, x_244);
x_246 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_246, 0, x_239);
lean_ctor_set(x_246, 1, x_240);
lean_ctor_set(x_246, 2, x_241);
lean_ctor_set(x_246, 3, x_242);
lean_ctor_set_uint8(x_246, sizeof(void*)*4, x_244);
x_247 = 0;
lean_ctor_set(x_1, 3, x_246);
lean_ctor_set(x_1, 2, x_238);
lean_ctor_set(x_1, 1, x_237);
lean_ctor_set(x_1, 0, x_245);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_247);
return x_1;
}
}
else
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_204);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; 
x_249 = lean_ctor_get(x_204, 3);
lean_dec(x_249);
x_250 = lean_ctor_get(x_204, 0);
lean_dec(x_250);
x_251 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_251);
x_252 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_252);
return x_1;
}
else
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; uint8_t x_257; 
x_253 = lean_ctor_get(x_204, 1);
x_254 = lean_ctor_get(x_204, 2);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_204);
x_255 = 0;
x_256 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_256, 0, x_205);
lean_ctor_set(x_256, 1, x_253);
lean_ctor_set(x_256, 2, x_254);
lean_ctor_set(x_256, 3, x_206);
lean_ctor_set_uint8(x_256, sizeof(void*)*4, x_255);
x_257 = 1;
lean_ctor_set(x_1, 3, x_256);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_257);
return x_1;
}
}
}
}
else
{
uint8_t x_258; 
x_258 = lean_ctor_get_uint8(x_205, sizeof(void*)*4);
if (x_258 == 0)
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_204);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_204, 0);
lean_dec(x_260);
x_261 = !lean_is_exclusive(x_205);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_267; 
x_262 = lean_ctor_get(x_205, 0);
x_263 = lean_ctor_get(x_205, 1);
x_264 = lean_ctor_get(x_205, 2);
x_265 = lean_ctor_get(x_205, 3);
x_266 = 1;
lean_ctor_set(x_205, 3, x_262);
lean_ctor_set(x_205, 2, x_35);
lean_ctor_set(x_205, 1, x_34);
lean_ctor_set(x_205, 0, x_33);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_266);
lean_ctor_set(x_204, 0, x_265);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_266);
x_267 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_264);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_205);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_267);
return x_1;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; uint8_t x_274; 
x_268 = lean_ctor_get(x_205, 0);
x_269 = lean_ctor_get(x_205, 1);
x_270 = lean_ctor_get(x_205, 2);
x_271 = lean_ctor_get(x_205, 3);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_205);
x_272 = 1;
x_273 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_273, 0, x_33);
lean_ctor_set(x_273, 1, x_34);
lean_ctor_set(x_273, 2, x_35);
lean_ctor_set(x_273, 3, x_268);
lean_ctor_set_uint8(x_273, sizeof(void*)*4, x_272);
lean_ctor_set(x_204, 0, x_271);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_272);
x_274 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_270);
lean_ctor_set(x_1, 1, x_269);
lean_ctor_set(x_1, 0, x_273);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_274);
return x_1;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_275 = lean_ctor_get(x_204, 1);
x_276 = lean_ctor_get(x_204, 2);
x_277 = lean_ctor_get(x_204, 3);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_204);
x_278 = lean_ctor_get(x_205, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_205, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_205, 2);
lean_inc(x_280);
x_281 = lean_ctor_get(x_205, 3);
lean_inc(x_281);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_282 = x_205;
} else {
 lean_dec_ref(x_205);
 x_282 = lean_box(0);
}
x_283 = 1;
if (lean_is_scalar(x_282)) {
 x_284 = lean_alloc_ctor(1, 4, 1);
} else {
 x_284 = x_282;
}
lean_ctor_set(x_284, 0, x_33);
lean_ctor_set(x_284, 1, x_34);
lean_ctor_set(x_284, 2, x_35);
lean_ctor_set(x_284, 3, x_278);
lean_ctor_set_uint8(x_284, sizeof(void*)*4, x_283);
x_285 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_285, 0, x_281);
lean_ctor_set(x_285, 1, x_275);
lean_ctor_set(x_285, 2, x_276);
lean_ctor_set(x_285, 3, x_277);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_283);
x_286 = 0;
lean_ctor_set(x_1, 3, x_285);
lean_ctor_set(x_1, 2, x_280);
lean_ctor_set(x_1, 1, x_279);
lean_ctor_set(x_1, 0, x_284);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_286);
return x_1;
}
}
else
{
lean_object* x_287; 
x_287 = lean_ctor_get(x_204, 3);
lean_inc(x_287);
if (lean_obj_tag(x_287) == 0)
{
uint8_t x_288; 
x_288 = !lean_is_exclusive(x_204);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; uint8_t x_291; uint8_t x_292; 
x_289 = lean_ctor_get(x_204, 3);
lean_dec(x_289);
x_290 = lean_ctor_get(x_204, 0);
lean_dec(x_290);
x_291 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_291);
x_292 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_292);
return x_1;
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; uint8_t x_297; 
x_293 = lean_ctor_get(x_204, 1);
x_294 = lean_ctor_get(x_204, 2);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_204);
x_295 = 0;
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_205);
lean_ctor_set(x_296, 1, x_293);
lean_ctor_set(x_296, 2, x_294);
lean_ctor_set(x_296, 3, x_287);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_295);
x_297 = 1;
lean_ctor_set(x_1, 3, x_296);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_297);
return x_1;
}
}
else
{
uint8_t x_298; 
x_298 = lean_ctor_get_uint8(x_287, sizeof(void*)*4);
if (x_298 == 0)
{
uint8_t x_299; 
lean_free_object(x_1);
x_299 = !lean_is_exclusive(x_204);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_300 = lean_ctor_get(x_204, 3);
lean_dec(x_300);
x_301 = lean_ctor_get(x_204, 0);
lean_dec(x_301);
x_302 = !lean_is_exclusive(x_287);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; uint8_t x_308; 
x_303 = lean_ctor_get(x_287, 0);
x_304 = lean_ctor_get(x_287, 1);
x_305 = lean_ctor_get(x_287, 2);
x_306 = lean_ctor_get(x_287, 3);
x_307 = 1;
lean_inc(x_205);
lean_ctor_set(x_287, 3, x_205);
lean_ctor_set(x_287, 2, x_35);
lean_ctor_set(x_287, 1, x_34);
lean_ctor_set(x_287, 0, x_33);
x_308 = !lean_is_exclusive(x_205);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_309 = lean_ctor_get(x_205, 3);
lean_dec(x_309);
x_310 = lean_ctor_get(x_205, 2);
lean_dec(x_310);
x_311 = lean_ctor_get(x_205, 1);
lean_dec(x_311);
x_312 = lean_ctor_get(x_205, 0);
lean_dec(x_312);
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_307);
lean_ctor_set(x_205, 3, x_306);
lean_ctor_set(x_205, 2, x_305);
lean_ctor_set(x_205, 1, x_304);
lean_ctor_set(x_205, 0, x_303);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_307);
x_313 = 0;
lean_ctor_set(x_204, 3, x_205);
lean_ctor_set(x_204, 0, x_287);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_313);
return x_204;
}
else
{
lean_object* x_314; uint8_t x_315; 
lean_dec(x_205);
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_307);
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_303);
lean_ctor_set(x_314, 1, x_304);
lean_ctor_set(x_314, 2, x_305);
lean_ctor_set(x_314, 3, x_306);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_307);
x_315 = 0;
lean_ctor_set(x_204, 3, x_314);
lean_ctor_set(x_204, 0, x_287);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_315);
return x_204;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_316 = lean_ctor_get(x_287, 0);
x_317 = lean_ctor_get(x_287, 1);
x_318 = lean_ctor_get(x_287, 2);
x_319 = lean_ctor_get(x_287, 3);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_287);
x_320 = 1;
lean_inc(x_205);
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_33);
lean_ctor_set(x_321, 1, x_34);
lean_ctor_set(x_321, 2, x_35);
lean_ctor_set(x_321, 3, x_205);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_322 = x_205;
} else {
 lean_dec_ref(x_205);
 x_322 = lean_box(0);
}
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_320);
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 4, 1);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_316);
lean_ctor_set(x_323, 1, x_317);
lean_ctor_set(x_323, 2, x_318);
lean_ctor_set(x_323, 3, x_319);
lean_ctor_set_uint8(x_323, sizeof(void*)*4, x_320);
x_324 = 0;
lean_ctor_set(x_204, 3, x_323);
lean_ctor_set(x_204, 0, x_321);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_324);
return x_204;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; 
x_325 = lean_ctor_get(x_204, 1);
x_326 = lean_ctor_get(x_204, 2);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_204);
x_327 = lean_ctor_get(x_287, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_287, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_287, 2);
lean_inc(x_329);
x_330 = lean_ctor_get(x_287, 3);
lean_inc(x_330);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 lean_ctor_release(x_287, 2);
 lean_ctor_release(x_287, 3);
 x_331 = x_287;
} else {
 lean_dec_ref(x_287);
 x_331 = lean_box(0);
}
x_332 = 1;
lean_inc(x_205);
if (lean_is_scalar(x_331)) {
 x_333 = lean_alloc_ctor(1, 4, 1);
} else {
 x_333 = x_331;
}
lean_ctor_set(x_333, 0, x_33);
lean_ctor_set(x_333, 1, x_34);
lean_ctor_set(x_333, 2, x_35);
lean_ctor_set(x_333, 3, x_205);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_334 = x_205;
} else {
 lean_dec_ref(x_205);
 x_334 = lean_box(0);
}
lean_ctor_set_uint8(x_333, sizeof(void*)*4, x_332);
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 4, 1);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_327);
lean_ctor_set(x_335, 1, x_328);
lean_ctor_set(x_335, 2, x_329);
lean_ctor_set(x_335, 3, x_330);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_332);
x_336 = 0;
x_337 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_337, 0, x_333);
lean_ctor_set(x_337, 1, x_325);
lean_ctor_set(x_337, 2, x_326);
lean_ctor_set(x_337, 3, x_335);
lean_ctor_set_uint8(x_337, sizeof(void*)*4, x_336);
return x_337;
}
}
else
{
uint8_t x_338; 
x_338 = !lean_is_exclusive(x_204);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_339 = lean_ctor_get(x_204, 3);
lean_dec(x_339);
x_340 = lean_ctor_get(x_204, 0);
lean_dec(x_340);
x_341 = !lean_is_exclusive(x_205);
if (x_341 == 0)
{
uint8_t x_342; uint8_t x_343; 
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_298);
x_342 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_342);
x_343 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_343);
return x_1;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; uint8_t x_350; 
x_344 = lean_ctor_get(x_205, 0);
x_345 = lean_ctor_get(x_205, 1);
x_346 = lean_ctor_get(x_205, 2);
x_347 = lean_ctor_get(x_205, 3);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_205);
x_348 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_348, 0, x_344);
lean_ctor_set(x_348, 1, x_345);
lean_ctor_set(x_348, 2, x_346);
lean_ctor_set(x_348, 3, x_347);
lean_ctor_set_uint8(x_348, sizeof(void*)*4, x_298);
x_349 = 0;
lean_ctor_set(x_204, 0, x_348);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_349);
x_350 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_350);
return x_1;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; uint8_t x_361; 
x_351 = lean_ctor_get(x_204, 1);
x_352 = lean_ctor_get(x_204, 2);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_204);
x_353 = lean_ctor_get(x_205, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_205, 1);
lean_inc(x_354);
x_355 = lean_ctor_get(x_205, 2);
lean_inc(x_355);
x_356 = lean_ctor_get(x_205, 3);
lean_inc(x_356);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_357 = x_205;
} else {
 lean_dec_ref(x_205);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 4, 1);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_353);
lean_ctor_set(x_358, 1, x_354);
lean_ctor_set(x_358, 2, x_355);
lean_ctor_set(x_358, 3, x_356);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_298);
x_359 = 0;
x_360 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_351);
lean_ctor_set(x_360, 2, x_352);
lean_ctor_set(x_360, 3, x_287);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
x_361 = 1;
lean_ctor_set(x_1, 3, x_360);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_361);
return x_1;
}
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
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_362 = lean_ctor_get(x_1, 0);
x_363 = lean_ctor_get(x_1, 1);
x_364 = lean_ctor_get(x_1, 2);
x_365 = lean_ctor_get(x_1, 3);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_1);
x_366 = l_Lean_Name_quickCmp(x_2, x_363);
switch (x_366) {
case 0:
{
uint8_t x_367; 
x_367 = l_Std_RBNode_isRed___rarg(x_362);
if (x_367 == 0)
{
lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_368 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_362, x_2, x_3);
x_369 = 1;
x_370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_363);
lean_ctor_set(x_370, 2, x_364);
lean_ctor_set(x_370, 3, x_365);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_369);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; 
x_371 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_362, x_2, x_3);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; 
x_373 = lean_ctor_get(x_371, 3);
lean_inc(x_373);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; 
x_374 = lean_ctor_get(x_371, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_371, 2);
lean_inc(x_375);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_376 = x_371;
} else {
 lean_dec_ref(x_371);
 x_376 = lean_box(0);
}
x_377 = 0;
if (lean_is_scalar(x_376)) {
 x_378 = lean_alloc_ctor(1, 4, 1);
} else {
 x_378 = x_376;
}
lean_ctor_set(x_378, 0, x_373);
lean_ctor_set(x_378, 1, x_374);
lean_ctor_set(x_378, 2, x_375);
lean_ctor_set(x_378, 3, x_373);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_377);
x_379 = 1;
x_380 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_363);
lean_ctor_set(x_380, 2, x_364);
lean_ctor_set(x_380, 3, x_365);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_379);
return x_380;
}
else
{
uint8_t x_381; 
x_381 = lean_ctor_get_uint8(x_373, sizeof(void*)*4);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; 
x_382 = lean_ctor_get(x_371, 1);
lean_inc(x_382);
x_383 = lean_ctor_get(x_371, 2);
lean_inc(x_383);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_384 = x_371;
} else {
 lean_dec_ref(x_371);
 x_384 = lean_box(0);
}
x_385 = lean_ctor_get(x_373, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_373, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_373, 2);
lean_inc(x_387);
x_388 = lean_ctor_get(x_373, 3);
lean_inc(x_388);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 lean_ctor_release(x_373, 2);
 lean_ctor_release(x_373, 3);
 x_389 = x_373;
} else {
 lean_dec_ref(x_373);
 x_389 = lean_box(0);
}
x_390 = 1;
if (lean_is_scalar(x_389)) {
 x_391 = lean_alloc_ctor(1, 4, 1);
} else {
 x_391 = x_389;
}
lean_ctor_set(x_391, 0, x_372);
lean_ctor_set(x_391, 1, x_382);
lean_ctor_set(x_391, 2, x_383);
lean_ctor_set(x_391, 3, x_385);
lean_ctor_set_uint8(x_391, sizeof(void*)*4, x_390);
if (lean_is_scalar(x_384)) {
 x_392 = lean_alloc_ctor(1, 4, 1);
} else {
 x_392 = x_384;
}
lean_ctor_set(x_392, 0, x_388);
lean_ctor_set(x_392, 1, x_363);
lean_ctor_set(x_392, 2, x_364);
lean_ctor_set(x_392, 3, x_365);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_390);
x_393 = 0;
x_394 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_386);
lean_ctor_set(x_394, 2, x_387);
lean_ctor_set(x_394, 3, x_392);
lean_ctor_set_uint8(x_394, sizeof(void*)*4, x_393);
return x_394;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; 
x_395 = lean_ctor_get(x_371, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_371, 2);
lean_inc(x_396);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_397 = x_371;
} else {
 lean_dec_ref(x_371);
 x_397 = lean_box(0);
}
x_398 = 0;
if (lean_is_scalar(x_397)) {
 x_399 = lean_alloc_ctor(1, 4, 1);
} else {
 x_399 = x_397;
}
lean_ctor_set(x_399, 0, x_372);
lean_ctor_set(x_399, 1, x_395);
lean_ctor_set(x_399, 2, x_396);
lean_ctor_set(x_399, 3, x_373);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_398);
x_400 = 1;
x_401 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_363);
lean_ctor_set(x_401, 2, x_364);
lean_ctor_set(x_401, 3, x_365);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_400);
return x_401;
}
}
}
else
{
uint8_t x_402; 
x_402 = lean_ctor_get_uint8(x_372, sizeof(void*)*4);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; lean_object* x_416; 
x_403 = lean_ctor_get(x_371, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_371, 2);
lean_inc(x_404);
x_405 = lean_ctor_get(x_371, 3);
lean_inc(x_405);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_406 = x_371;
} else {
 lean_dec_ref(x_371);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_372, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_372, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_372, 2);
lean_inc(x_409);
x_410 = lean_ctor_get(x_372, 3);
lean_inc(x_410);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_411 = x_372;
} else {
 lean_dec_ref(x_372);
 x_411 = lean_box(0);
}
x_412 = 1;
if (lean_is_scalar(x_411)) {
 x_413 = lean_alloc_ctor(1, 4, 1);
} else {
 x_413 = x_411;
}
lean_ctor_set(x_413, 0, x_407);
lean_ctor_set(x_413, 1, x_408);
lean_ctor_set(x_413, 2, x_409);
lean_ctor_set(x_413, 3, x_410);
lean_ctor_set_uint8(x_413, sizeof(void*)*4, x_412);
if (lean_is_scalar(x_406)) {
 x_414 = lean_alloc_ctor(1, 4, 1);
} else {
 x_414 = x_406;
}
lean_ctor_set(x_414, 0, x_405);
lean_ctor_set(x_414, 1, x_363);
lean_ctor_set(x_414, 2, x_364);
lean_ctor_set(x_414, 3, x_365);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_412);
x_415 = 0;
x_416 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_416, 0, x_413);
lean_ctor_set(x_416, 1, x_403);
lean_ctor_set(x_416, 2, x_404);
lean_ctor_set(x_416, 3, x_414);
lean_ctor_set_uint8(x_416, sizeof(void*)*4, x_415);
return x_416;
}
else
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_371, 3);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; uint8_t x_423; lean_object* x_424; 
x_418 = lean_ctor_get(x_371, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_371, 2);
lean_inc(x_419);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_420 = x_371;
} else {
 lean_dec_ref(x_371);
 x_420 = lean_box(0);
}
x_421 = 0;
if (lean_is_scalar(x_420)) {
 x_422 = lean_alloc_ctor(1, 4, 1);
} else {
 x_422 = x_420;
}
lean_ctor_set(x_422, 0, x_372);
lean_ctor_set(x_422, 1, x_418);
lean_ctor_set(x_422, 2, x_419);
lean_ctor_set(x_422, 3, x_417);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
x_423 = 1;
x_424 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_363);
lean_ctor_set(x_424, 2, x_364);
lean_ctor_set(x_424, 3, x_365);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_423);
return x_424;
}
else
{
uint8_t x_425; 
x_425 = lean_ctor_get_uint8(x_417, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; 
x_426 = lean_ctor_get(x_371, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_371, 2);
lean_inc(x_427);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_428 = x_371;
} else {
 lean_dec_ref(x_371);
 x_428 = lean_box(0);
}
x_429 = lean_ctor_get(x_417, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_417, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_417, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_417, 3);
lean_inc(x_432);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_433 = x_417;
} else {
 lean_dec_ref(x_417);
 x_433 = lean_box(0);
}
x_434 = 1;
lean_inc(x_372);
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(1, 4, 1);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_372);
lean_ctor_set(x_435, 1, x_426);
lean_ctor_set(x_435, 2, x_427);
lean_ctor_set(x_435, 3, x_429);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_436 = x_372;
} else {
 lean_dec_ref(x_372);
 x_436 = lean_box(0);
}
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_434);
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 4, 1);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_432);
lean_ctor_set(x_437, 1, x_363);
lean_ctor_set(x_437, 2, x_364);
lean_ctor_set(x_437, 3, x_365);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_434);
x_438 = 0;
if (lean_is_scalar(x_428)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_428;
}
lean_ctor_set(x_439, 0, x_435);
lean_ctor_set(x_439, 1, x_430);
lean_ctor_set(x_439, 2, x_431);
lean_ctor_set(x_439, 3, x_437);
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
return x_439;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; 
x_440 = lean_ctor_get(x_371, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_371, 2);
lean_inc(x_441);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_442 = x_371;
} else {
 lean_dec_ref(x_371);
 x_442 = lean_box(0);
}
x_443 = lean_ctor_get(x_372, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_372, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_372, 2);
lean_inc(x_445);
x_446 = lean_ctor_get(x_372, 3);
lean_inc(x_446);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_447 = x_372;
} else {
 lean_dec_ref(x_372);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 4, 1);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_443);
lean_ctor_set(x_448, 1, x_444);
lean_ctor_set(x_448, 2, x_445);
lean_ctor_set(x_448, 3, x_446);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_425);
x_449 = 0;
if (lean_is_scalar(x_442)) {
 x_450 = lean_alloc_ctor(1, 4, 1);
} else {
 x_450 = x_442;
}
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_440);
lean_ctor_set(x_450, 2, x_441);
lean_ctor_set(x_450, 3, x_417);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
x_451 = 1;
x_452 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_452, 0, x_450);
lean_ctor_set(x_452, 1, x_363);
lean_ctor_set(x_452, 2, x_364);
lean_ctor_set(x_452, 3, x_365);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_451);
return x_452;
}
}
}
}
}
}
case 1:
{
uint8_t x_453; lean_object* x_454; 
lean_dec(x_364);
lean_dec(x_363);
x_453 = 1;
x_454 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_454, 0, x_362);
lean_ctor_set(x_454, 1, x_2);
lean_ctor_set(x_454, 2, x_3);
lean_ctor_set(x_454, 3, x_365);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_453);
return x_454;
}
default: 
{
uint8_t x_455; 
x_455 = l_Std_RBNode_isRed___rarg(x_365);
if (x_455 == 0)
{
lean_object* x_456; uint8_t x_457; lean_object* x_458; 
x_456 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_365, x_2, x_3);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_362);
lean_ctor_set(x_458, 1, x_363);
lean_ctor_set(x_458, 2, x_364);
lean_ctor_set(x_458, 3, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
else
{
lean_object* x_459; lean_object* x_460; 
x_459 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_365, x_2, x_3);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; 
x_461 = lean_ctor_get(x_459, 3);
lean_inc(x_461);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; 
x_462 = lean_ctor_get(x_459, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_459, 2);
lean_inc(x_463);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_464 = x_459;
} else {
 lean_dec_ref(x_459);
 x_464 = lean_box(0);
}
x_465 = 0;
if (lean_is_scalar(x_464)) {
 x_466 = lean_alloc_ctor(1, 4, 1);
} else {
 x_466 = x_464;
}
lean_ctor_set(x_466, 0, x_461);
lean_ctor_set(x_466, 1, x_462);
lean_ctor_set(x_466, 2, x_463);
lean_ctor_set(x_466, 3, x_461);
lean_ctor_set_uint8(x_466, sizeof(void*)*4, x_465);
x_467 = 1;
x_468 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_468, 0, x_362);
lean_ctor_set(x_468, 1, x_363);
lean_ctor_set(x_468, 2, x_364);
lean_ctor_set(x_468, 3, x_466);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_467);
return x_468;
}
else
{
uint8_t x_469; 
x_469 = lean_ctor_get_uint8(x_461, sizeof(void*)*4);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; uint8_t x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; lean_object* x_482; 
x_470 = lean_ctor_get(x_459, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_459, 2);
lean_inc(x_471);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_472 = x_459;
} else {
 lean_dec_ref(x_459);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_461, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_461, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_461, 2);
lean_inc(x_475);
x_476 = lean_ctor_get(x_461, 3);
lean_inc(x_476);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 lean_ctor_release(x_461, 2);
 lean_ctor_release(x_461, 3);
 x_477 = x_461;
} else {
 lean_dec_ref(x_461);
 x_477 = lean_box(0);
}
x_478 = 1;
if (lean_is_scalar(x_477)) {
 x_479 = lean_alloc_ctor(1, 4, 1);
} else {
 x_479 = x_477;
}
lean_ctor_set(x_479, 0, x_362);
lean_ctor_set(x_479, 1, x_363);
lean_ctor_set(x_479, 2, x_364);
lean_ctor_set(x_479, 3, x_460);
lean_ctor_set_uint8(x_479, sizeof(void*)*4, x_478);
if (lean_is_scalar(x_472)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_472;
}
lean_ctor_set(x_480, 0, x_473);
lean_ctor_set(x_480, 1, x_474);
lean_ctor_set(x_480, 2, x_475);
lean_ctor_set(x_480, 3, x_476);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_478);
x_481 = 0;
x_482 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_482, 0, x_479);
lean_ctor_set(x_482, 1, x_470);
lean_ctor_set(x_482, 2, x_471);
lean_ctor_set(x_482, 3, x_480);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_481);
return x_482;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; 
x_483 = lean_ctor_get(x_459, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_459, 2);
lean_inc(x_484);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_485 = x_459;
} else {
 lean_dec_ref(x_459);
 x_485 = lean_box(0);
}
x_486 = 0;
if (lean_is_scalar(x_485)) {
 x_487 = lean_alloc_ctor(1, 4, 1);
} else {
 x_487 = x_485;
}
lean_ctor_set(x_487, 0, x_460);
lean_ctor_set(x_487, 1, x_483);
lean_ctor_set(x_487, 2, x_484);
lean_ctor_set(x_487, 3, x_461);
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_486);
x_488 = 1;
x_489 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_489, 0, x_362);
lean_ctor_set(x_489, 1, x_363);
lean_ctor_set(x_489, 2, x_364);
lean_ctor_set(x_489, 3, x_487);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_488);
return x_489;
}
}
}
else
{
uint8_t x_490; 
x_490 = lean_ctor_get_uint8(x_460, sizeof(void*)*4);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; lean_object* x_504; 
x_491 = lean_ctor_get(x_459, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_459, 2);
lean_inc(x_492);
x_493 = lean_ctor_get(x_459, 3);
lean_inc(x_493);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_494 = x_459;
} else {
 lean_dec_ref(x_459);
 x_494 = lean_box(0);
}
x_495 = lean_ctor_get(x_460, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_460, 1);
lean_inc(x_496);
x_497 = lean_ctor_get(x_460, 2);
lean_inc(x_497);
x_498 = lean_ctor_get(x_460, 3);
lean_inc(x_498);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_499 = x_460;
} else {
 lean_dec_ref(x_460);
 x_499 = lean_box(0);
}
x_500 = 1;
if (lean_is_scalar(x_499)) {
 x_501 = lean_alloc_ctor(1, 4, 1);
} else {
 x_501 = x_499;
}
lean_ctor_set(x_501, 0, x_362);
lean_ctor_set(x_501, 1, x_363);
lean_ctor_set(x_501, 2, x_364);
lean_ctor_set(x_501, 3, x_495);
lean_ctor_set_uint8(x_501, sizeof(void*)*4, x_500);
if (lean_is_scalar(x_494)) {
 x_502 = lean_alloc_ctor(1, 4, 1);
} else {
 x_502 = x_494;
}
lean_ctor_set(x_502, 0, x_498);
lean_ctor_set(x_502, 1, x_491);
lean_ctor_set(x_502, 2, x_492);
lean_ctor_set(x_502, 3, x_493);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_500);
x_503 = 0;
x_504 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_496);
lean_ctor_set(x_504, 2, x_497);
lean_ctor_set(x_504, 3, x_502);
lean_ctor_set_uint8(x_504, sizeof(void*)*4, x_503);
return x_504;
}
else
{
lean_object* x_505; 
x_505 = lean_ctor_get(x_459, 3);
lean_inc(x_505);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; uint8_t x_511; lean_object* x_512; 
x_506 = lean_ctor_get(x_459, 1);
lean_inc(x_506);
x_507 = lean_ctor_get(x_459, 2);
lean_inc(x_507);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_508 = x_459;
} else {
 lean_dec_ref(x_459);
 x_508 = lean_box(0);
}
x_509 = 0;
if (lean_is_scalar(x_508)) {
 x_510 = lean_alloc_ctor(1, 4, 1);
} else {
 x_510 = x_508;
}
lean_ctor_set(x_510, 0, x_460);
lean_ctor_set(x_510, 1, x_506);
lean_ctor_set(x_510, 2, x_507);
lean_ctor_set(x_510, 3, x_505);
lean_ctor_set_uint8(x_510, sizeof(void*)*4, x_509);
x_511 = 1;
x_512 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_512, 0, x_362);
lean_ctor_set(x_512, 1, x_363);
lean_ctor_set(x_512, 2, x_364);
lean_ctor_set(x_512, 3, x_510);
lean_ctor_set_uint8(x_512, sizeof(void*)*4, x_511);
return x_512;
}
else
{
uint8_t x_513; 
x_513 = lean_ctor_get_uint8(x_505, sizeof(void*)*4);
if (x_513 == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; 
x_514 = lean_ctor_get(x_459, 1);
lean_inc(x_514);
x_515 = lean_ctor_get(x_459, 2);
lean_inc(x_515);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_516 = x_459;
} else {
 lean_dec_ref(x_459);
 x_516 = lean_box(0);
}
x_517 = lean_ctor_get(x_505, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_505, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_505, 2);
lean_inc(x_519);
x_520 = lean_ctor_get(x_505, 3);
lean_inc(x_520);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 lean_ctor_release(x_505, 2);
 lean_ctor_release(x_505, 3);
 x_521 = x_505;
} else {
 lean_dec_ref(x_505);
 x_521 = lean_box(0);
}
x_522 = 1;
lean_inc(x_460);
if (lean_is_scalar(x_521)) {
 x_523 = lean_alloc_ctor(1, 4, 1);
} else {
 x_523 = x_521;
}
lean_ctor_set(x_523, 0, x_362);
lean_ctor_set(x_523, 1, x_363);
lean_ctor_set(x_523, 2, x_364);
lean_ctor_set(x_523, 3, x_460);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_524 = x_460;
} else {
 lean_dec_ref(x_460);
 x_524 = lean_box(0);
}
lean_ctor_set_uint8(x_523, sizeof(void*)*4, x_522);
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(1, 4, 1);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_517);
lean_ctor_set(x_525, 1, x_518);
lean_ctor_set(x_525, 2, x_519);
lean_ctor_set(x_525, 3, x_520);
lean_ctor_set_uint8(x_525, sizeof(void*)*4, x_522);
x_526 = 0;
if (lean_is_scalar(x_516)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_516;
}
lean_ctor_set(x_527, 0, x_523);
lean_ctor_set(x_527, 1, x_514);
lean_ctor_set(x_527, 2, x_515);
lean_ctor_set(x_527, 3, x_525);
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
return x_527;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; uint8_t x_537; lean_object* x_538; uint8_t x_539; lean_object* x_540; 
x_528 = lean_ctor_get(x_459, 1);
lean_inc(x_528);
x_529 = lean_ctor_get(x_459, 2);
lean_inc(x_529);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_530 = x_459;
} else {
 lean_dec_ref(x_459);
 x_530 = lean_box(0);
}
x_531 = lean_ctor_get(x_460, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_460, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_460, 2);
lean_inc(x_533);
x_534 = lean_ctor_get(x_460, 3);
lean_inc(x_534);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_535 = x_460;
} else {
 lean_dec_ref(x_460);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 4, 1);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_531);
lean_ctor_set(x_536, 1, x_532);
lean_ctor_set(x_536, 2, x_533);
lean_ctor_set(x_536, 3, x_534);
lean_ctor_set_uint8(x_536, sizeof(void*)*4, x_513);
x_537 = 0;
if (lean_is_scalar(x_530)) {
 x_538 = lean_alloc_ctor(1, 4, 1);
} else {
 x_538 = x_530;
}
lean_ctor_set(x_538, 0, x_536);
lean_ctor_set(x_538, 1, x_528);
lean_ctor_set(x_538, 2, x_529);
lean_ctor_set(x_538, 3, x_505);
lean_ctor_set_uint8(x_538, sizeof(void*)*4, x_537);
x_539 = 1;
x_540 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_540, 0, x_362);
lean_ctor_set(x_540, 1, x_363);
lean_ctor_set(x_540, 2, x_364);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_539);
return x_540;
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
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_13 = l_Lean_Name_quickCmp(x_2, x_10);
switch (x_13) {
case 0:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_9, x_2, x_3);
x_15 = 0;
lean_ctor_set(x_1, 0, x_14);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
case 1:
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
default: 
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_12, x_2, x_3);
x_18 = 0;
lean_ctor_set(x_1, 3, x_17);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_18);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_23 = l_Lean_Name_quickCmp(x_2, x_20);
switch (x_23) {
case 0:
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_19, x_2, x_3);
x_25 = 0;
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_25);
return x_26;
}
case 1:
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
default: 
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_22, x_2, x_3);
x_30 = 0;
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 2);
x_36 = lean_ctor_get(x_1, 3);
x_37 = l_Lean_Name_quickCmp(x_2, x_34);
switch (x_37) {
case 0:
{
uint8_t x_38; 
x_38 = l_Std_RBNode_isRed___rarg(x_33);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_33, x_2, x_3);
x_40 = 1;
lean_ctor_set(x_1, 0, x_39);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_40);
return x_1;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_33, x_2, x_3);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 3);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_41, 3);
lean_dec(x_45);
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = 0;
lean_ctor_set(x_41, 0, x_43);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_47);
x_48 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_41, 1);
x_50 = lean_ctor_get(x_41, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = 0;
x_52 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 2, x_50);
lean_ctor_set(x_52, 3, x_43);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_51);
x_53 = 1;
lean_ctor_set(x_1, 0, x_52);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_53);
return x_1;
}
}
else
{
uint8_t x_54; 
x_54 = lean_ctor_get_uint8(x_43, sizeof(void*)*4);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_41);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_41, 1);
x_57 = lean_ctor_get(x_41, 2);
x_58 = lean_ctor_get(x_41, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_41, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_43);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_43, 0);
x_62 = lean_ctor_get(x_43, 1);
x_63 = lean_ctor_get(x_43, 2);
x_64 = lean_ctor_get(x_43, 3);
x_65 = 1;
lean_ctor_set(x_43, 3, x_61);
lean_ctor_set(x_43, 2, x_57);
lean_ctor_set(x_43, 1, x_56);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_65);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_64);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_65);
x_66 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_63);
lean_ctor_set(x_1, 1, x_62);
lean_ctor_set(x_1, 0, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; 
x_67 = lean_ctor_get(x_43, 0);
x_68 = lean_ctor_get(x_43, 1);
x_69 = lean_ctor_get(x_43, 2);
x_70 = lean_ctor_get(x_43, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_43);
x_71 = 1;
x_72 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_72, 0, x_42);
lean_ctor_set(x_72, 1, x_56);
lean_ctor_set(x_72, 2, x_57);
lean_ctor_set(x_72, 3, x_67);
lean_ctor_set_uint8(x_72, sizeof(void*)*4, x_71);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_70);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_71);
x_73 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_69);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_72);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_73);
return x_1;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_74 = lean_ctor_get(x_41, 1);
x_75 = lean_ctor_get(x_41, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_41);
x_76 = lean_ctor_get(x_43, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_43, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_43, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_43, 3);
lean_inc(x_79);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_80 = x_43;
} else {
 lean_dec_ref(x_43);
 x_80 = lean_box(0);
}
x_81 = 1;
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(1, 4, 1);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_42);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_75);
lean_ctor_set(x_82, 3, x_76);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_81);
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_34);
lean_ctor_set(x_83, 2, x_35);
lean_ctor_set(x_83, 3, x_36);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_81);
x_84 = 0;
lean_ctor_set(x_1, 3, x_83);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_82);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_84);
return x_1;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_41);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_41, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_41, 0);
lean_dec(x_87);
x_88 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_88);
x_89 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_89);
return x_1;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_41, 1);
x_91 = lean_ctor_get(x_41, 2);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_41);
x_92 = 0;
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_42);
lean_ctor_set(x_93, 1, x_90);
lean_ctor_set(x_93, 2, x_91);
lean_ctor_set(x_93, 3, x_43);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_92);
x_94 = 1;
lean_ctor_set(x_1, 0, x_93);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_94);
return x_1;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_42, sizeof(void*)*4);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_41);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_41, 1);
x_98 = lean_ctor_get(x_41, 2);
x_99 = lean_ctor_get(x_41, 3);
x_100 = lean_ctor_get(x_41, 0);
lean_dec(x_100);
x_101 = !lean_is_exclusive(x_42);
if (x_101 == 0)
{
uint8_t x_102; uint8_t x_103; 
x_102 = 1;
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_102);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_102);
x_103 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_42);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_103);
return x_1;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; uint8_t x_110; 
x_104 = lean_ctor_get(x_42, 0);
x_105 = lean_ctor_get(x_42, 1);
x_106 = lean_ctor_get(x_42, 2);
x_107 = lean_ctor_get(x_42, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_42);
x_108 = 1;
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_105);
lean_ctor_set(x_109, 2, x_106);
lean_ctor_set(x_109, 3, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_108);
x_110 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_110);
return x_1;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_111 = lean_ctor_get(x_41, 1);
x_112 = lean_ctor_get(x_41, 2);
x_113 = lean_ctor_get(x_41, 3);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_41);
x_114 = lean_ctor_get(x_42, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_42, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_42, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_42, 3);
lean_inc(x_117);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_118 = x_42;
} else {
 lean_dec_ref(x_42);
 x_118 = lean_box(0);
}
x_119 = 1;
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(1, 4, 1);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_114);
lean_ctor_set(x_120, 1, x_115);
lean_ctor_set(x_120, 2, x_116);
lean_ctor_set(x_120, 3, x_117);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_119);
x_121 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_121, 0, x_113);
lean_ctor_set(x_121, 1, x_34);
lean_ctor_set(x_121, 2, x_35);
lean_ctor_set(x_121, 3, x_36);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_119);
x_122 = 0;
lean_ctor_set(x_1, 3, x_121);
lean_ctor_set(x_1, 2, x_112);
lean_ctor_set(x_1, 1, x_111);
lean_ctor_set(x_1, 0, x_120);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_122);
return x_1;
}
}
else
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_41, 3);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_41);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_41, 3);
lean_dec(x_125);
x_126 = lean_ctor_get(x_41, 0);
lean_dec(x_126);
x_127 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_127);
x_128 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_128);
return x_1;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_41, 1);
x_130 = lean_ctor_get(x_41, 2);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_41);
x_131 = 0;
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_42);
lean_ctor_set(x_132, 1, x_129);
lean_ctor_set(x_132, 2, x_130);
lean_ctor_set(x_132, 3, x_123);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_131);
x_133 = 1;
lean_ctor_set(x_1, 0, x_132);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_133);
return x_1;
}
}
else
{
uint8_t x_134; 
x_134 = lean_ctor_get_uint8(x_123, sizeof(void*)*4);
if (x_134 == 0)
{
uint8_t x_135; 
lean_free_object(x_1);
x_135 = !lean_is_exclusive(x_41);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_41, 1);
x_137 = lean_ctor_get(x_41, 2);
x_138 = lean_ctor_get(x_41, 3);
lean_dec(x_138);
x_139 = lean_ctor_get(x_41, 0);
lean_dec(x_139);
x_140 = !lean_is_exclusive(x_123);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; 
x_141 = lean_ctor_get(x_123, 0);
x_142 = lean_ctor_get(x_123, 1);
x_143 = lean_ctor_get(x_123, 2);
x_144 = lean_ctor_get(x_123, 3);
x_145 = 1;
lean_inc(x_42);
lean_ctor_set(x_123, 3, x_141);
lean_ctor_set(x_123, 2, x_137);
lean_ctor_set(x_123, 1, x_136);
lean_ctor_set(x_123, 0, x_42);
x_146 = !lean_is_exclusive(x_42);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_147 = lean_ctor_get(x_42, 3);
lean_dec(x_147);
x_148 = lean_ctor_get(x_42, 2);
lean_dec(x_148);
x_149 = lean_ctor_get(x_42, 1);
lean_dec(x_149);
x_150 = lean_ctor_get(x_42, 0);
lean_dec(x_150);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_145);
lean_ctor_set(x_42, 3, x_36);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 0, x_144);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_145);
x_151 = 0;
lean_ctor_set(x_41, 3, x_42);
lean_ctor_set(x_41, 2, x_143);
lean_ctor_set(x_41, 1, x_142);
lean_ctor_set(x_41, 0, x_123);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_151);
return x_41;
}
else
{
lean_object* x_152; uint8_t x_153; 
lean_dec(x_42);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_145);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_34);
lean_ctor_set(x_152, 2, x_35);
lean_ctor_set(x_152, 3, x_36);
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_145);
x_153 = 0;
lean_ctor_set(x_41, 3, x_152);
lean_ctor_set(x_41, 2, x_143);
lean_ctor_set(x_41, 1, x_142);
lean_ctor_set(x_41, 0, x_123);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_153);
return x_41;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_154 = lean_ctor_get(x_123, 0);
x_155 = lean_ctor_get(x_123, 1);
x_156 = lean_ctor_get(x_123, 2);
x_157 = lean_ctor_get(x_123, 3);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_123);
x_158 = 1;
lean_inc(x_42);
x_159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_159, 0, x_42);
lean_ctor_set(x_159, 1, x_136);
lean_ctor_set(x_159, 2, x_137);
lean_ctor_set(x_159, 3, x_154);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_160 = x_42;
} else {
 lean_dec_ref(x_42);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_158);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_157);
lean_ctor_set(x_161, 1, x_34);
lean_ctor_set(x_161, 2, x_35);
lean_ctor_set(x_161, 3, x_36);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_158);
x_162 = 0;
lean_ctor_set(x_41, 3, x_161);
lean_ctor_set(x_41, 2, x_156);
lean_ctor_set(x_41, 1, x_155);
lean_ctor_set(x_41, 0, x_159);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_162);
return x_41;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; 
x_163 = lean_ctor_get(x_41, 1);
x_164 = lean_ctor_get(x_41, 2);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_41);
x_165 = lean_ctor_get(x_123, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_123, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_123, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_123, 3);
lean_inc(x_168);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 x_169 = x_123;
} else {
 lean_dec_ref(x_123);
 x_169 = lean_box(0);
}
x_170 = 1;
lean_inc(x_42);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(1, 4, 1);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_42);
lean_ctor_set(x_171, 1, x_163);
lean_ctor_set(x_171, 2, x_164);
lean_ctor_set(x_171, 3, x_165);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_172 = x_42;
} else {
 lean_dec_ref(x_42);
 x_172 = lean_box(0);
}
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_170);
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 4, 1);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_34);
lean_ctor_set(x_173, 2, x_35);
lean_ctor_set(x_173, 3, x_36);
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_170);
x_174 = 0;
x_175 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_166);
lean_ctor_set(x_175, 2, x_167);
lean_ctor_set(x_175, 3, x_173);
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_174);
return x_175;
}
}
else
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_41);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = lean_ctor_get(x_41, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_41, 0);
lean_dec(x_178);
x_179 = !lean_is_exclusive(x_42);
if (x_179 == 0)
{
uint8_t x_180; uint8_t x_181; 
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_134);
x_180 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_180);
x_181 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_181);
return x_1;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_188; 
x_182 = lean_ctor_get(x_42, 0);
x_183 = lean_ctor_get(x_42, 1);
x_184 = lean_ctor_get(x_42, 2);
x_185 = lean_ctor_get(x_42, 3);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_42);
x_186 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_183);
lean_ctor_set(x_186, 2, x_184);
lean_ctor_set(x_186, 3, x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_134);
x_187 = 0;
lean_ctor_set(x_41, 0, x_186);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_187);
x_188 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; uint8_t x_199; 
x_189 = lean_ctor_get(x_41, 1);
x_190 = lean_ctor_get(x_41, 2);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_41);
x_191 = lean_ctor_get(x_42, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_42, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_42, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_42, 3);
lean_inc(x_194);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_195 = x_42;
} else {
 lean_dec_ref(x_42);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 4, 1);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_191);
lean_ctor_set(x_196, 1, x_192);
lean_ctor_set(x_196, 2, x_193);
lean_ctor_set(x_196, 3, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_134);
x_197 = 0;
x_198 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_189);
lean_ctor_set(x_198, 2, x_190);
lean_ctor_set(x_198, 3, x_123);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_197);
x_199 = 1;
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
}
}
}
}
}
case 1:
{
uint8_t x_200; 
lean_dec(x_35);
lean_dec(x_34);
x_200 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
default: 
{
uint8_t x_201; 
x_201 = l_Std_RBNode_isRed___rarg(x_36);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_36, x_2, x_3);
x_203 = 1;
lean_ctor_set(x_1, 3, x_202);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_203);
return x_1;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_36, x_2, x_3);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_204, 3);
lean_inc(x_206);
if (lean_obj_tag(x_206) == 0)
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_204);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_211; 
x_208 = lean_ctor_get(x_204, 3);
lean_dec(x_208);
x_209 = lean_ctor_get(x_204, 0);
lean_dec(x_209);
x_210 = 0;
lean_ctor_set(x_204, 0, x_206);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_210);
x_211 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_211);
return x_1;
}
else
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; uint8_t x_216; 
x_212 = lean_ctor_get(x_204, 1);
x_213 = lean_ctor_get(x_204, 2);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_204);
x_214 = 0;
x_215 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_215, 0, x_206);
lean_ctor_set(x_215, 1, x_212);
lean_ctor_set(x_215, 2, x_213);
lean_ctor_set(x_215, 3, x_206);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_214);
x_216 = 1;
lean_ctor_set(x_1, 3, x_215);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_216);
return x_1;
}
}
else
{
uint8_t x_217; 
x_217 = lean_ctor_get_uint8(x_206, sizeof(void*)*4);
if (x_217 == 0)
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_204);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_219 = lean_ctor_get(x_204, 1);
x_220 = lean_ctor_get(x_204, 2);
x_221 = lean_ctor_get(x_204, 3);
lean_dec(x_221);
x_222 = lean_ctor_get(x_204, 0);
lean_dec(x_222);
x_223 = !lean_is_exclusive(x_206);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_229; 
x_224 = lean_ctor_get(x_206, 0);
x_225 = lean_ctor_get(x_206, 1);
x_226 = lean_ctor_get(x_206, 2);
x_227 = lean_ctor_get(x_206, 3);
x_228 = 1;
lean_ctor_set(x_206, 3, x_205);
lean_ctor_set(x_206, 2, x_35);
lean_ctor_set(x_206, 1, x_34);
lean_ctor_set(x_206, 0, x_33);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_228);
lean_ctor_set(x_204, 3, x_227);
lean_ctor_set(x_204, 2, x_226);
lean_ctor_set(x_204, 1, x_225);
lean_ctor_set(x_204, 0, x_224);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_228);
x_229 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_229);
return x_1;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; uint8_t x_236; 
x_230 = lean_ctor_get(x_206, 0);
x_231 = lean_ctor_get(x_206, 1);
x_232 = lean_ctor_get(x_206, 2);
x_233 = lean_ctor_get(x_206, 3);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_206);
x_234 = 1;
x_235 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_235, 0, x_33);
lean_ctor_set(x_235, 1, x_34);
lean_ctor_set(x_235, 2, x_35);
lean_ctor_set(x_235, 3, x_205);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_234);
lean_ctor_set(x_204, 3, x_233);
lean_ctor_set(x_204, 2, x_232);
lean_ctor_set(x_204, 1, x_231);
lean_ctor_set(x_204, 0, x_230);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_234);
x_236 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_237 = lean_ctor_get(x_204, 1);
x_238 = lean_ctor_get(x_204, 2);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_204);
x_239 = lean_ctor_get(x_206, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_206, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_206, 2);
lean_inc(x_241);
x_242 = lean_ctor_get(x_206, 3);
lean_inc(x_242);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 lean_ctor_release(x_206, 2);
 lean_ctor_release(x_206, 3);
 x_243 = x_206;
} else {
 lean_dec_ref(x_206);
 x_243 = lean_box(0);
}
x_244 = 1;
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(1, 4, 1);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_33);
lean_ctor_set(x_245, 1, x_34);
lean_ctor_set(x_245, 2, x_35);
lean_ctor_set(x_245, 3, x_205);
lean_ctor_set_uint8(x_245, sizeof(void*)*4, x_244);
x_246 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_246, 0, x_239);
lean_ctor_set(x_246, 1, x_240);
lean_ctor_set(x_246, 2, x_241);
lean_ctor_set(x_246, 3, x_242);
lean_ctor_set_uint8(x_246, sizeof(void*)*4, x_244);
x_247 = 0;
lean_ctor_set(x_1, 3, x_246);
lean_ctor_set(x_1, 2, x_238);
lean_ctor_set(x_1, 1, x_237);
lean_ctor_set(x_1, 0, x_245);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_247);
return x_1;
}
}
else
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_204);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; 
x_249 = lean_ctor_get(x_204, 3);
lean_dec(x_249);
x_250 = lean_ctor_get(x_204, 0);
lean_dec(x_250);
x_251 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_251);
x_252 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_252);
return x_1;
}
else
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; uint8_t x_257; 
x_253 = lean_ctor_get(x_204, 1);
x_254 = lean_ctor_get(x_204, 2);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_204);
x_255 = 0;
x_256 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_256, 0, x_205);
lean_ctor_set(x_256, 1, x_253);
lean_ctor_set(x_256, 2, x_254);
lean_ctor_set(x_256, 3, x_206);
lean_ctor_set_uint8(x_256, sizeof(void*)*4, x_255);
x_257 = 1;
lean_ctor_set(x_1, 3, x_256);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_257);
return x_1;
}
}
}
}
else
{
uint8_t x_258; 
x_258 = lean_ctor_get_uint8(x_205, sizeof(void*)*4);
if (x_258 == 0)
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_204);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_204, 0);
lean_dec(x_260);
x_261 = !lean_is_exclusive(x_205);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_267; 
x_262 = lean_ctor_get(x_205, 0);
x_263 = lean_ctor_get(x_205, 1);
x_264 = lean_ctor_get(x_205, 2);
x_265 = lean_ctor_get(x_205, 3);
x_266 = 1;
lean_ctor_set(x_205, 3, x_262);
lean_ctor_set(x_205, 2, x_35);
lean_ctor_set(x_205, 1, x_34);
lean_ctor_set(x_205, 0, x_33);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_266);
lean_ctor_set(x_204, 0, x_265);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_266);
x_267 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_264);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_205);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_267);
return x_1;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; uint8_t x_274; 
x_268 = lean_ctor_get(x_205, 0);
x_269 = lean_ctor_get(x_205, 1);
x_270 = lean_ctor_get(x_205, 2);
x_271 = lean_ctor_get(x_205, 3);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_205);
x_272 = 1;
x_273 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_273, 0, x_33);
lean_ctor_set(x_273, 1, x_34);
lean_ctor_set(x_273, 2, x_35);
lean_ctor_set(x_273, 3, x_268);
lean_ctor_set_uint8(x_273, sizeof(void*)*4, x_272);
lean_ctor_set(x_204, 0, x_271);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_272);
x_274 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_270);
lean_ctor_set(x_1, 1, x_269);
lean_ctor_set(x_1, 0, x_273);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_274);
return x_1;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_275 = lean_ctor_get(x_204, 1);
x_276 = lean_ctor_get(x_204, 2);
x_277 = lean_ctor_get(x_204, 3);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_204);
x_278 = lean_ctor_get(x_205, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_205, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_205, 2);
lean_inc(x_280);
x_281 = lean_ctor_get(x_205, 3);
lean_inc(x_281);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_282 = x_205;
} else {
 lean_dec_ref(x_205);
 x_282 = lean_box(0);
}
x_283 = 1;
if (lean_is_scalar(x_282)) {
 x_284 = lean_alloc_ctor(1, 4, 1);
} else {
 x_284 = x_282;
}
lean_ctor_set(x_284, 0, x_33);
lean_ctor_set(x_284, 1, x_34);
lean_ctor_set(x_284, 2, x_35);
lean_ctor_set(x_284, 3, x_278);
lean_ctor_set_uint8(x_284, sizeof(void*)*4, x_283);
x_285 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_285, 0, x_281);
lean_ctor_set(x_285, 1, x_275);
lean_ctor_set(x_285, 2, x_276);
lean_ctor_set(x_285, 3, x_277);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_283);
x_286 = 0;
lean_ctor_set(x_1, 3, x_285);
lean_ctor_set(x_1, 2, x_280);
lean_ctor_set(x_1, 1, x_279);
lean_ctor_set(x_1, 0, x_284);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_286);
return x_1;
}
}
else
{
lean_object* x_287; 
x_287 = lean_ctor_get(x_204, 3);
lean_inc(x_287);
if (lean_obj_tag(x_287) == 0)
{
uint8_t x_288; 
x_288 = !lean_is_exclusive(x_204);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; uint8_t x_291; uint8_t x_292; 
x_289 = lean_ctor_get(x_204, 3);
lean_dec(x_289);
x_290 = lean_ctor_get(x_204, 0);
lean_dec(x_290);
x_291 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_291);
x_292 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_292);
return x_1;
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; uint8_t x_297; 
x_293 = lean_ctor_get(x_204, 1);
x_294 = lean_ctor_get(x_204, 2);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_204);
x_295 = 0;
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_205);
lean_ctor_set(x_296, 1, x_293);
lean_ctor_set(x_296, 2, x_294);
lean_ctor_set(x_296, 3, x_287);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_295);
x_297 = 1;
lean_ctor_set(x_1, 3, x_296);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_297);
return x_1;
}
}
else
{
uint8_t x_298; 
x_298 = lean_ctor_get_uint8(x_287, sizeof(void*)*4);
if (x_298 == 0)
{
uint8_t x_299; 
lean_free_object(x_1);
x_299 = !lean_is_exclusive(x_204);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_300 = lean_ctor_get(x_204, 3);
lean_dec(x_300);
x_301 = lean_ctor_get(x_204, 0);
lean_dec(x_301);
x_302 = !lean_is_exclusive(x_287);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; uint8_t x_308; 
x_303 = lean_ctor_get(x_287, 0);
x_304 = lean_ctor_get(x_287, 1);
x_305 = lean_ctor_get(x_287, 2);
x_306 = lean_ctor_get(x_287, 3);
x_307 = 1;
lean_inc(x_205);
lean_ctor_set(x_287, 3, x_205);
lean_ctor_set(x_287, 2, x_35);
lean_ctor_set(x_287, 1, x_34);
lean_ctor_set(x_287, 0, x_33);
x_308 = !lean_is_exclusive(x_205);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_309 = lean_ctor_get(x_205, 3);
lean_dec(x_309);
x_310 = lean_ctor_get(x_205, 2);
lean_dec(x_310);
x_311 = lean_ctor_get(x_205, 1);
lean_dec(x_311);
x_312 = lean_ctor_get(x_205, 0);
lean_dec(x_312);
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_307);
lean_ctor_set(x_205, 3, x_306);
lean_ctor_set(x_205, 2, x_305);
lean_ctor_set(x_205, 1, x_304);
lean_ctor_set(x_205, 0, x_303);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_307);
x_313 = 0;
lean_ctor_set(x_204, 3, x_205);
lean_ctor_set(x_204, 0, x_287);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_313);
return x_204;
}
else
{
lean_object* x_314; uint8_t x_315; 
lean_dec(x_205);
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_307);
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_303);
lean_ctor_set(x_314, 1, x_304);
lean_ctor_set(x_314, 2, x_305);
lean_ctor_set(x_314, 3, x_306);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_307);
x_315 = 0;
lean_ctor_set(x_204, 3, x_314);
lean_ctor_set(x_204, 0, x_287);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_315);
return x_204;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_316 = lean_ctor_get(x_287, 0);
x_317 = lean_ctor_get(x_287, 1);
x_318 = lean_ctor_get(x_287, 2);
x_319 = lean_ctor_get(x_287, 3);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_287);
x_320 = 1;
lean_inc(x_205);
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_33);
lean_ctor_set(x_321, 1, x_34);
lean_ctor_set(x_321, 2, x_35);
lean_ctor_set(x_321, 3, x_205);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_322 = x_205;
} else {
 lean_dec_ref(x_205);
 x_322 = lean_box(0);
}
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_320);
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 4, 1);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_316);
lean_ctor_set(x_323, 1, x_317);
lean_ctor_set(x_323, 2, x_318);
lean_ctor_set(x_323, 3, x_319);
lean_ctor_set_uint8(x_323, sizeof(void*)*4, x_320);
x_324 = 0;
lean_ctor_set(x_204, 3, x_323);
lean_ctor_set(x_204, 0, x_321);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_324);
return x_204;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; 
x_325 = lean_ctor_get(x_204, 1);
x_326 = lean_ctor_get(x_204, 2);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_204);
x_327 = lean_ctor_get(x_287, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_287, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_287, 2);
lean_inc(x_329);
x_330 = lean_ctor_get(x_287, 3);
lean_inc(x_330);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 lean_ctor_release(x_287, 2);
 lean_ctor_release(x_287, 3);
 x_331 = x_287;
} else {
 lean_dec_ref(x_287);
 x_331 = lean_box(0);
}
x_332 = 1;
lean_inc(x_205);
if (lean_is_scalar(x_331)) {
 x_333 = lean_alloc_ctor(1, 4, 1);
} else {
 x_333 = x_331;
}
lean_ctor_set(x_333, 0, x_33);
lean_ctor_set(x_333, 1, x_34);
lean_ctor_set(x_333, 2, x_35);
lean_ctor_set(x_333, 3, x_205);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_334 = x_205;
} else {
 lean_dec_ref(x_205);
 x_334 = lean_box(0);
}
lean_ctor_set_uint8(x_333, sizeof(void*)*4, x_332);
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 4, 1);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_327);
lean_ctor_set(x_335, 1, x_328);
lean_ctor_set(x_335, 2, x_329);
lean_ctor_set(x_335, 3, x_330);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_332);
x_336 = 0;
x_337 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_337, 0, x_333);
lean_ctor_set(x_337, 1, x_325);
lean_ctor_set(x_337, 2, x_326);
lean_ctor_set(x_337, 3, x_335);
lean_ctor_set_uint8(x_337, sizeof(void*)*4, x_336);
return x_337;
}
}
else
{
uint8_t x_338; 
x_338 = !lean_is_exclusive(x_204);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_339 = lean_ctor_get(x_204, 3);
lean_dec(x_339);
x_340 = lean_ctor_get(x_204, 0);
lean_dec(x_340);
x_341 = !lean_is_exclusive(x_205);
if (x_341 == 0)
{
uint8_t x_342; uint8_t x_343; 
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_298);
x_342 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_342);
x_343 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_343);
return x_1;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; uint8_t x_350; 
x_344 = lean_ctor_get(x_205, 0);
x_345 = lean_ctor_get(x_205, 1);
x_346 = lean_ctor_get(x_205, 2);
x_347 = lean_ctor_get(x_205, 3);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_205);
x_348 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_348, 0, x_344);
lean_ctor_set(x_348, 1, x_345);
lean_ctor_set(x_348, 2, x_346);
lean_ctor_set(x_348, 3, x_347);
lean_ctor_set_uint8(x_348, sizeof(void*)*4, x_298);
x_349 = 0;
lean_ctor_set(x_204, 0, x_348);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_349);
x_350 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_350);
return x_1;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; uint8_t x_361; 
x_351 = lean_ctor_get(x_204, 1);
x_352 = lean_ctor_get(x_204, 2);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_204);
x_353 = lean_ctor_get(x_205, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_205, 1);
lean_inc(x_354);
x_355 = lean_ctor_get(x_205, 2);
lean_inc(x_355);
x_356 = lean_ctor_get(x_205, 3);
lean_inc(x_356);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_357 = x_205;
} else {
 lean_dec_ref(x_205);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 4, 1);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_353);
lean_ctor_set(x_358, 1, x_354);
lean_ctor_set(x_358, 2, x_355);
lean_ctor_set(x_358, 3, x_356);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_298);
x_359 = 0;
x_360 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_351);
lean_ctor_set(x_360, 2, x_352);
lean_ctor_set(x_360, 3, x_287);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
x_361 = 1;
lean_ctor_set(x_1, 3, x_360);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_361);
return x_1;
}
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
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_362 = lean_ctor_get(x_1, 0);
x_363 = lean_ctor_get(x_1, 1);
x_364 = lean_ctor_get(x_1, 2);
x_365 = lean_ctor_get(x_1, 3);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_1);
x_366 = l_Lean_Name_quickCmp(x_2, x_363);
switch (x_366) {
case 0:
{
uint8_t x_367; 
x_367 = l_Std_RBNode_isRed___rarg(x_362);
if (x_367 == 0)
{
lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_368 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_362, x_2, x_3);
x_369 = 1;
x_370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_363);
lean_ctor_set(x_370, 2, x_364);
lean_ctor_set(x_370, 3, x_365);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_369);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; 
x_371 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_362, x_2, x_3);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; 
x_373 = lean_ctor_get(x_371, 3);
lean_inc(x_373);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; 
x_374 = lean_ctor_get(x_371, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_371, 2);
lean_inc(x_375);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_376 = x_371;
} else {
 lean_dec_ref(x_371);
 x_376 = lean_box(0);
}
x_377 = 0;
if (lean_is_scalar(x_376)) {
 x_378 = lean_alloc_ctor(1, 4, 1);
} else {
 x_378 = x_376;
}
lean_ctor_set(x_378, 0, x_373);
lean_ctor_set(x_378, 1, x_374);
lean_ctor_set(x_378, 2, x_375);
lean_ctor_set(x_378, 3, x_373);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_377);
x_379 = 1;
x_380 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_363);
lean_ctor_set(x_380, 2, x_364);
lean_ctor_set(x_380, 3, x_365);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_379);
return x_380;
}
else
{
uint8_t x_381; 
x_381 = lean_ctor_get_uint8(x_373, sizeof(void*)*4);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; 
x_382 = lean_ctor_get(x_371, 1);
lean_inc(x_382);
x_383 = lean_ctor_get(x_371, 2);
lean_inc(x_383);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_384 = x_371;
} else {
 lean_dec_ref(x_371);
 x_384 = lean_box(0);
}
x_385 = lean_ctor_get(x_373, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_373, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_373, 2);
lean_inc(x_387);
x_388 = lean_ctor_get(x_373, 3);
lean_inc(x_388);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 lean_ctor_release(x_373, 2);
 lean_ctor_release(x_373, 3);
 x_389 = x_373;
} else {
 lean_dec_ref(x_373);
 x_389 = lean_box(0);
}
x_390 = 1;
if (lean_is_scalar(x_389)) {
 x_391 = lean_alloc_ctor(1, 4, 1);
} else {
 x_391 = x_389;
}
lean_ctor_set(x_391, 0, x_372);
lean_ctor_set(x_391, 1, x_382);
lean_ctor_set(x_391, 2, x_383);
lean_ctor_set(x_391, 3, x_385);
lean_ctor_set_uint8(x_391, sizeof(void*)*4, x_390);
if (lean_is_scalar(x_384)) {
 x_392 = lean_alloc_ctor(1, 4, 1);
} else {
 x_392 = x_384;
}
lean_ctor_set(x_392, 0, x_388);
lean_ctor_set(x_392, 1, x_363);
lean_ctor_set(x_392, 2, x_364);
lean_ctor_set(x_392, 3, x_365);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_390);
x_393 = 0;
x_394 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_386);
lean_ctor_set(x_394, 2, x_387);
lean_ctor_set(x_394, 3, x_392);
lean_ctor_set_uint8(x_394, sizeof(void*)*4, x_393);
return x_394;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; 
x_395 = lean_ctor_get(x_371, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_371, 2);
lean_inc(x_396);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_397 = x_371;
} else {
 lean_dec_ref(x_371);
 x_397 = lean_box(0);
}
x_398 = 0;
if (lean_is_scalar(x_397)) {
 x_399 = lean_alloc_ctor(1, 4, 1);
} else {
 x_399 = x_397;
}
lean_ctor_set(x_399, 0, x_372);
lean_ctor_set(x_399, 1, x_395);
lean_ctor_set(x_399, 2, x_396);
lean_ctor_set(x_399, 3, x_373);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_398);
x_400 = 1;
x_401 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_363);
lean_ctor_set(x_401, 2, x_364);
lean_ctor_set(x_401, 3, x_365);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_400);
return x_401;
}
}
}
else
{
uint8_t x_402; 
x_402 = lean_ctor_get_uint8(x_372, sizeof(void*)*4);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; lean_object* x_416; 
x_403 = lean_ctor_get(x_371, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_371, 2);
lean_inc(x_404);
x_405 = lean_ctor_get(x_371, 3);
lean_inc(x_405);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_406 = x_371;
} else {
 lean_dec_ref(x_371);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_372, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_372, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_372, 2);
lean_inc(x_409);
x_410 = lean_ctor_get(x_372, 3);
lean_inc(x_410);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_411 = x_372;
} else {
 lean_dec_ref(x_372);
 x_411 = lean_box(0);
}
x_412 = 1;
if (lean_is_scalar(x_411)) {
 x_413 = lean_alloc_ctor(1, 4, 1);
} else {
 x_413 = x_411;
}
lean_ctor_set(x_413, 0, x_407);
lean_ctor_set(x_413, 1, x_408);
lean_ctor_set(x_413, 2, x_409);
lean_ctor_set(x_413, 3, x_410);
lean_ctor_set_uint8(x_413, sizeof(void*)*4, x_412);
if (lean_is_scalar(x_406)) {
 x_414 = lean_alloc_ctor(1, 4, 1);
} else {
 x_414 = x_406;
}
lean_ctor_set(x_414, 0, x_405);
lean_ctor_set(x_414, 1, x_363);
lean_ctor_set(x_414, 2, x_364);
lean_ctor_set(x_414, 3, x_365);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_412);
x_415 = 0;
x_416 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_416, 0, x_413);
lean_ctor_set(x_416, 1, x_403);
lean_ctor_set(x_416, 2, x_404);
lean_ctor_set(x_416, 3, x_414);
lean_ctor_set_uint8(x_416, sizeof(void*)*4, x_415);
return x_416;
}
else
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_371, 3);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; uint8_t x_423; lean_object* x_424; 
x_418 = lean_ctor_get(x_371, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_371, 2);
lean_inc(x_419);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_420 = x_371;
} else {
 lean_dec_ref(x_371);
 x_420 = lean_box(0);
}
x_421 = 0;
if (lean_is_scalar(x_420)) {
 x_422 = lean_alloc_ctor(1, 4, 1);
} else {
 x_422 = x_420;
}
lean_ctor_set(x_422, 0, x_372);
lean_ctor_set(x_422, 1, x_418);
lean_ctor_set(x_422, 2, x_419);
lean_ctor_set(x_422, 3, x_417);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
x_423 = 1;
x_424 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_363);
lean_ctor_set(x_424, 2, x_364);
lean_ctor_set(x_424, 3, x_365);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_423);
return x_424;
}
else
{
uint8_t x_425; 
x_425 = lean_ctor_get_uint8(x_417, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; 
x_426 = lean_ctor_get(x_371, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_371, 2);
lean_inc(x_427);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_428 = x_371;
} else {
 lean_dec_ref(x_371);
 x_428 = lean_box(0);
}
x_429 = lean_ctor_get(x_417, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_417, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_417, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_417, 3);
lean_inc(x_432);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_433 = x_417;
} else {
 lean_dec_ref(x_417);
 x_433 = lean_box(0);
}
x_434 = 1;
lean_inc(x_372);
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(1, 4, 1);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_372);
lean_ctor_set(x_435, 1, x_426);
lean_ctor_set(x_435, 2, x_427);
lean_ctor_set(x_435, 3, x_429);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_436 = x_372;
} else {
 lean_dec_ref(x_372);
 x_436 = lean_box(0);
}
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_434);
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 4, 1);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_432);
lean_ctor_set(x_437, 1, x_363);
lean_ctor_set(x_437, 2, x_364);
lean_ctor_set(x_437, 3, x_365);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_434);
x_438 = 0;
if (lean_is_scalar(x_428)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_428;
}
lean_ctor_set(x_439, 0, x_435);
lean_ctor_set(x_439, 1, x_430);
lean_ctor_set(x_439, 2, x_431);
lean_ctor_set(x_439, 3, x_437);
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
return x_439;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; 
x_440 = lean_ctor_get(x_371, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_371, 2);
lean_inc(x_441);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_442 = x_371;
} else {
 lean_dec_ref(x_371);
 x_442 = lean_box(0);
}
x_443 = lean_ctor_get(x_372, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_372, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_372, 2);
lean_inc(x_445);
x_446 = lean_ctor_get(x_372, 3);
lean_inc(x_446);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_447 = x_372;
} else {
 lean_dec_ref(x_372);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 4, 1);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_443);
lean_ctor_set(x_448, 1, x_444);
lean_ctor_set(x_448, 2, x_445);
lean_ctor_set(x_448, 3, x_446);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_425);
x_449 = 0;
if (lean_is_scalar(x_442)) {
 x_450 = lean_alloc_ctor(1, 4, 1);
} else {
 x_450 = x_442;
}
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_440);
lean_ctor_set(x_450, 2, x_441);
lean_ctor_set(x_450, 3, x_417);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
x_451 = 1;
x_452 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_452, 0, x_450);
lean_ctor_set(x_452, 1, x_363);
lean_ctor_set(x_452, 2, x_364);
lean_ctor_set(x_452, 3, x_365);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_451);
return x_452;
}
}
}
}
}
}
case 1:
{
uint8_t x_453; lean_object* x_454; 
lean_dec(x_364);
lean_dec(x_363);
x_453 = 1;
x_454 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_454, 0, x_362);
lean_ctor_set(x_454, 1, x_2);
lean_ctor_set(x_454, 2, x_3);
lean_ctor_set(x_454, 3, x_365);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_453);
return x_454;
}
default: 
{
uint8_t x_455; 
x_455 = l_Std_RBNode_isRed___rarg(x_365);
if (x_455 == 0)
{
lean_object* x_456; uint8_t x_457; lean_object* x_458; 
x_456 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_365, x_2, x_3);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_362);
lean_ctor_set(x_458, 1, x_363);
lean_ctor_set(x_458, 2, x_364);
lean_ctor_set(x_458, 3, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
else
{
lean_object* x_459; lean_object* x_460; 
x_459 = l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_365, x_2, x_3);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; 
x_461 = lean_ctor_get(x_459, 3);
lean_inc(x_461);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; 
x_462 = lean_ctor_get(x_459, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_459, 2);
lean_inc(x_463);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_464 = x_459;
} else {
 lean_dec_ref(x_459);
 x_464 = lean_box(0);
}
x_465 = 0;
if (lean_is_scalar(x_464)) {
 x_466 = lean_alloc_ctor(1, 4, 1);
} else {
 x_466 = x_464;
}
lean_ctor_set(x_466, 0, x_461);
lean_ctor_set(x_466, 1, x_462);
lean_ctor_set(x_466, 2, x_463);
lean_ctor_set(x_466, 3, x_461);
lean_ctor_set_uint8(x_466, sizeof(void*)*4, x_465);
x_467 = 1;
x_468 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_468, 0, x_362);
lean_ctor_set(x_468, 1, x_363);
lean_ctor_set(x_468, 2, x_364);
lean_ctor_set(x_468, 3, x_466);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_467);
return x_468;
}
else
{
uint8_t x_469; 
x_469 = lean_ctor_get_uint8(x_461, sizeof(void*)*4);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; uint8_t x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; lean_object* x_482; 
x_470 = lean_ctor_get(x_459, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_459, 2);
lean_inc(x_471);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_472 = x_459;
} else {
 lean_dec_ref(x_459);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_461, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_461, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_461, 2);
lean_inc(x_475);
x_476 = lean_ctor_get(x_461, 3);
lean_inc(x_476);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 lean_ctor_release(x_461, 2);
 lean_ctor_release(x_461, 3);
 x_477 = x_461;
} else {
 lean_dec_ref(x_461);
 x_477 = lean_box(0);
}
x_478 = 1;
if (lean_is_scalar(x_477)) {
 x_479 = lean_alloc_ctor(1, 4, 1);
} else {
 x_479 = x_477;
}
lean_ctor_set(x_479, 0, x_362);
lean_ctor_set(x_479, 1, x_363);
lean_ctor_set(x_479, 2, x_364);
lean_ctor_set(x_479, 3, x_460);
lean_ctor_set_uint8(x_479, sizeof(void*)*4, x_478);
if (lean_is_scalar(x_472)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_472;
}
lean_ctor_set(x_480, 0, x_473);
lean_ctor_set(x_480, 1, x_474);
lean_ctor_set(x_480, 2, x_475);
lean_ctor_set(x_480, 3, x_476);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_478);
x_481 = 0;
x_482 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_482, 0, x_479);
lean_ctor_set(x_482, 1, x_470);
lean_ctor_set(x_482, 2, x_471);
lean_ctor_set(x_482, 3, x_480);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_481);
return x_482;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; 
x_483 = lean_ctor_get(x_459, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_459, 2);
lean_inc(x_484);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_485 = x_459;
} else {
 lean_dec_ref(x_459);
 x_485 = lean_box(0);
}
x_486 = 0;
if (lean_is_scalar(x_485)) {
 x_487 = lean_alloc_ctor(1, 4, 1);
} else {
 x_487 = x_485;
}
lean_ctor_set(x_487, 0, x_460);
lean_ctor_set(x_487, 1, x_483);
lean_ctor_set(x_487, 2, x_484);
lean_ctor_set(x_487, 3, x_461);
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_486);
x_488 = 1;
x_489 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_489, 0, x_362);
lean_ctor_set(x_489, 1, x_363);
lean_ctor_set(x_489, 2, x_364);
lean_ctor_set(x_489, 3, x_487);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_488);
return x_489;
}
}
}
else
{
uint8_t x_490; 
x_490 = lean_ctor_get_uint8(x_460, sizeof(void*)*4);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; lean_object* x_504; 
x_491 = lean_ctor_get(x_459, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_459, 2);
lean_inc(x_492);
x_493 = lean_ctor_get(x_459, 3);
lean_inc(x_493);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_494 = x_459;
} else {
 lean_dec_ref(x_459);
 x_494 = lean_box(0);
}
x_495 = lean_ctor_get(x_460, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_460, 1);
lean_inc(x_496);
x_497 = lean_ctor_get(x_460, 2);
lean_inc(x_497);
x_498 = lean_ctor_get(x_460, 3);
lean_inc(x_498);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_499 = x_460;
} else {
 lean_dec_ref(x_460);
 x_499 = lean_box(0);
}
x_500 = 1;
if (lean_is_scalar(x_499)) {
 x_501 = lean_alloc_ctor(1, 4, 1);
} else {
 x_501 = x_499;
}
lean_ctor_set(x_501, 0, x_362);
lean_ctor_set(x_501, 1, x_363);
lean_ctor_set(x_501, 2, x_364);
lean_ctor_set(x_501, 3, x_495);
lean_ctor_set_uint8(x_501, sizeof(void*)*4, x_500);
if (lean_is_scalar(x_494)) {
 x_502 = lean_alloc_ctor(1, 4, 1);
} else {
 x_502 = x_494;
}
lean_ctor_set(x_502, 0, x_498);
lean_ctor_set(x_502, 1, x_491);
lean_ctor_set(x_502, 2, x_492);
lean_ctor_set(x_502, 3, x_493);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_500);
x_503 = 0;
x_504 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_496);
lean_ctor_set(x_504, 2, x_497);
lean_ctor_set(x_504, 3, x_502);
lean_ctor_set_uint8(x_504, sizeof(void*)*4, x_503);
return x_504;
}
else
{
lean_object* x_505; 
x_505 = lean_ctor_get(x_459, 3);
lean_inc(x_505);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; uint8_t x_511; lean_object* x_512; 
x_506 = lean_ctor_get(x_459, 1);
lean_inc(x_506);
x_507 = lean_ctor_get(x_459, 2);
lean_inc(x_507);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_508 = x_459;
} else {
 lean_dec_ref(x_459);
 x_508 = lean_box(0);
}
x_509 = 0;
if (lean_is_scalar(x_508)) {
 x_510 = lean_alloc_ctor(1, 4, 1);
} else {
 x_510 = x_508;
}
lean_ctor_set(x_510, 0, x_460);
lean_ctor_set(x_510, 1, x_506);
lean_ctor_set(x_510, 2, x_507);
lean_ctor_set(x_510, 3, x_505);
lean_ctor_set_uint8(x_510, sizeof(void*)*4, x_509);
x_511 = 1;
x_512 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_512, 0, x_362);
lean_ctor_set(x_512, 1, x_363);
lean_ctor_set(x_512, 2, x_364);
lean_ctor_set(x_512, 3, x_510);
lean_ctor_set_uint8(x_512, sizeof(void*)*4, x_511);
return x_512;
}
else
{
uint8_t x_513; 
x_513 = lean_ctor_get_uint8(x_505, sizeof(void*)*4);
if (x_513 == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; 
x_514 = lean_ctor_get(x_459, 1);
lean_inc(x_514);
x_515 = lean_ctor_get(x_459, 2);
lean_inc(x_515);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_516 = x_459;
} else {
 lean_dec_ref(x_459);
 x_516 = lean_box(0);
}
x_517 = lean_ctor_get(x_505, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_505, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_505, 2);
lean_inc(x_519);
x_520 = lean_ctor_get(x_505, 3);
lean_inc(x_520);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 lean_ctor_release(x_505, 2);
 lean_ctor_release(x_505, 3);
 x_521 = x_505;
} else {
 lean_dec_ref(x_505);
 x_521 = lean_box(0);
}
x_522 = 1;
lean_inc(x_460);
if (lean_is_scalar(x_521)) {
 x_523 = lean_alloc_ctor(1, 4, 1);
} else {
 x_523 = x_521;
}
lean_ctor_set(x_523, 0, x_362);
lean_ctor_set(x_523, 1, x_363);
lean_ctor_set(x_523, 2, x_364);
lean_ctor_set(x_523, 3, x_460);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_524 = x_460;
} else {
 lean_dec_ref(x_460);
 x_524 = lean_box(0);
}
lean_ctor_set_uint8(x_523, sizeof(void*)*4, x_522);
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(1, 4, 1);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_517);
lean_ctor_set(x_525, 1, x_518);
lean_ctor_set(x_525, 2, x_519);
lean_ctor_set(x_525, 3, x_520);
lean_ctor_set_uint8(x_525, sizeof(void*)*4, x_522);
x_526 = 0;
if (lean_is_scalar(x_516)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_516;
}
lean_ctor_set(x_527, 0, x_523);
lean_ctor_set(x_527, 1, x_514);
lean_ctor_set(x_527, 2, x_515);
lean_ctor_set(x_527, 3, x_525);
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
return x_527;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; uint8_t x_537; lean_object* x_538; uint8_t x_539; lean_object* x_540; 
x_528 = lean_ctor_get(x_459, 1);
lean_inc(x_528);
x_529 = lean_ctor_get(x_459, 2);
lean_inc(x_529);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_530 = x_459;
} else {
 lean_dec_ref(x_459);
 x_530 = lean_box(0);
}
x_531 = lean_ctor_get(x_460, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_460, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_460, 2);
lean_inc(x_533);
x_534 = lean_ctor_get(x_460, 3);
lean_inc(x_534);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_535 = x_460;
} else {
 lean_dec_ref(x_460);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 4, 1);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_531);
lean_ctor_set(x_536, 1, x_532);
lean_ctor_set(x_536, 2, x_533);
lean_ctor_set(x_536, 3, x_534);
lean_ctor_set_uint8(x_536, sizeof(void*)*4, x_513);
x_537 = 0;
if (lean_is_scalar(x_530)) {
 x_538 = lean_alloc_ctor(1, 4, 1);
} else {
 x_538 = x_530;
}
lean_ctor_set(x_538, 0, x_536);
lean_ctor_set(x_538, 1, x_528);
lean_ctor_set(x_538, 2, x_529);
lean_ctor_set(x_538, 3, x_505);
lean_ctor_set_uint8(x_538, sizeof(void*)*4, x_537);
x_539 = 1;
x_540 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_540, 0, x_362);
lean_ctor_set(x_540, 1, x_363);
lean_ctor_set(x_540, 2, x_364);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_539);
return x_540;
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
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_insert___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabitedTokenMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollectionTokenMap(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_LeadingIdentBehavior_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
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
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7242_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_LeadingIdentBehavior_toCtorIdx(x_1);
x_4 = l_Lean_Parser_LeadingIdentBehavior_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7242____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7242_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_instBEqLeadingIdentBehavior___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7242____boxed), 2, 0);
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
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Parser.LeadingIdentBehavior.default");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__3;
x_2 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__2;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__4;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_incQuotDepth___closed__1;
x_2 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__2;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__6;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Parser.LeadingIdentBehavior.symbol");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__3;
x_2 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__9;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__11() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__10;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_incQuotDepth___closed__1;
x_2 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__9;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__13() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__12;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Parser.LeadingIdentBehavior.both");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__14;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__3;
x_2 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__15;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__17() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__16;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_incQuotDepth___closed__1;
x_2 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__15;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__19() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__18;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257_(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__5;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__7;
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
case 1:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1024u);
x_10 = lean_nat_dec_le(x_9, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__11;
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__13;
x_14 = l_Repr_addAppParen(x_13, x_2);
return x_14;
}
}
default: 
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_nat_dec_le(x_15, x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__17;
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__19;
x_20 = l_Repr_addAppParen(x_19, x_2);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_instReprLeadingIdentBehavior___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instReprLeadingIdentBehavior() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instReprLeadingIdentBehavior___closed__1;
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
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_box(0);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_5, 1);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_5, 1, x_18);
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
case 1:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_5, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg(x_1, x_24);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_box(0);
lean_ctor_set(x_5, 1, x_26);
return x_5;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_ctor_set(x_5, 1, x_27);
return x_5;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_5, 0);
lean_inc(x_28);
lean_dec(x_5);
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
lean_dec(x_15);
x_30 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg(x_1, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
case 2:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_5);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_5, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_dec(x_15);
x_38 = lean_box(0);
x_39 = lean_name_mk_string(x_38, x_37);
x_40 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg(x_1, x_39);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_box(0);
lean_ctor_set(x_5, 1, x_41);
return x_5;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
lean_ctor_set(x_5, 1, x_42);
return x_5;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_5, 0);
lean_inc(x_43);
lean_dec(x_5);
x_44 = lean_ctor_get(x_15, 1);
lean_inc(x_44);
lean_dec(x_15);
x_45 = lean_box(0);
x_46 = lean_name_mk_string(x_45, x_44);
x_47 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg(x_1, x_46);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
default: 
{
switch (x_4) {
case 0:
{
uint8_t x_52; 
lean_dec(x_15);
x_52 = !lean_is_exclusive(x_5);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_5, 1);
lean_dec(x_53);
x_54 = l_Lean_identKind;
x_55 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg(x_1, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_box(0);
lean_ctor_set(x_5, 1, x_56);
return x_5;
}
else
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
lean_ctor_set(x_5, 1, x_57);
return x_5;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_5, 0);
lean_inc(x_58);
lean_dec(x_5);
x_59 = l_Lean_identKind;
x_60 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg(x_1, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
case 1:
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_5);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_5, 1);
lean_dec(x_66);
x_67 = lean_ctor_get(x_15, 2);
lean_inc(x_67);
lean_dec(x_15);
x_68 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg(x_1, x_67);
lean_dec(x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_Lean_identKind;
x_70 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg(x_1, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_box(0);
lean_ctor_set(x_5, 1, x_71);
return x_5;
}
else
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
lean_ctor_set(x_5, 1, x_72);
return x_5;
}
}
else
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
lean_dec(x_68);
lean_ctor_set(x_5, 1, x_73);
return x_5;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_5, 0);
lean_inc(x_74);
lean_dec(x_5);
x_75 = lean_ctor_get(x_15, 2);
lean_inc(x_75);
lean_dec(x_15);
x_76 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg(x_1, x_75);
lean_dec(x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = l_Lean_identKind;
x_78 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg(x_1, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_74);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_74);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_76, 0);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_74);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
default: 
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_5);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_5, 1);
lean_dec(x_86);
x_87 = lean_ctor_get(x_15, 2);
lean_inc(x_87);
lean_dec(x_15);
x_88 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg(x_1, x_87);
lean_dec(x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_Lean_identKind;
x_90 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg(x_1, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_box(0);
lean_ctor_set(x_5, 1, x_91);
return x_5;
}
else
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec(x_90);
lean_ctor_set(x_5, 1, x_92);
return x_5;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_88, 0);
lean_inc(x_93);
lean_dec(x_88);
x_94 = l_Lean_identKind;
x_95 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg(x_1, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_ctor_set(x_5, 1, x_93);
return x_5;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec(x_95);
x_97 = l_List_appendTR___rarg(x_93, x_96);
lean_ctor_set(x_5, 1, x_97);
return x_5;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_5, 0);
lean_inc(x_98);
lean_dec(x_5);
x_99 = lean_ctor_get(x_15, 2);
lean_inc(x_99);
lean_dec(x_15);
x_100 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg(x_1, x_99);
lean_dec(x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = l_Lean_identKind;
x_102 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg(x_1, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_98);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 0);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_98);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_100, 0);
lean_inc(x_107);
lean_dec(x_100);
x_108 = l_Lean_identKind;
x_109 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg(x_1, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_98);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
lean_dec(x_109);
x_112 = l_List_appendTR___rarg(x_107, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_98);
lean_ctor_set(x_113, 1, x_112);
return x_113;
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
LEAN_EXPORT lean_object* l_Lean_Parser_indexed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_indexed___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7595____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_whitespace(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7595____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7595____lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7595_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7595____closed__1;
x_3 = l_IO_mkRef___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7595____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7595____lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7614____lambda__1(lean_object* x_1) {
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
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7614____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7614____lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7614_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7614____closed__1;
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_categoryParserFnExtension___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_categoryParserFnExtension___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Parser_categoryParserFnExtension___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_instInhabitedParserFn___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___lambda__1___closed__1;
return x_2;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__1;
x_2 = lean_alloc_closure((void*)(l_instInhabitedDepArrow___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Environment");
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.EnvExtensionInterfaceUnsafe.getState");
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__3;
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__4;
x_3 = lean_unsigned_to_nat(223u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_array_get_size(x_7);
x_9 = lean_nat_dec_lt(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__2;
x_11 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__5;
x_12 = lean_panic_fn(x_10, x_11);
x_13 = lean_apply_3(x_12, x_3, x_4, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_fget(x_7, x_6);
x_15 = x_14;
x_16 = lean_apply_3(x_15, x_3, x_4, x_5);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Parser_categoryParserFnExtension;
x_7 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1(x_6, x_5, x_1, x_2, x_3);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 2);
lean_dec(x_6);
lean_ctor_set(x_3, 2, x_2);
x_7 = l_Lean_Parser_categoryParserFn(x_1, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 3);
x_11 = lean_ctor_get(x_3, 4);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_ctor_get(x_3, 6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_2);
lean_ctor_set(x_15, 3, x_10);
lean_ctor_set(x_15, 4, x_11);
lean_ctor_set(x_15, 5, x_13);
lean_ctor_set(x_15, 6, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*7, x_12);
x_16 = l_Lean_Parser_categoryParserFn(x_1, x_15, x_4);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_categoryParser___elambda__1), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = l_Lean_Parser_errorAtSavedPos___closed__2;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_termParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("term");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_termParser___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_termParser___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_termParser___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___elambda__1(lean_object* x_1, lean_object* x_2) {
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
x_8 = lean_ctor_get(x_2, 2);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(0);
x_14 = l_Lean_Parser_checkNoImmediateColon___elambda__1___closed__1;
x_15 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_14, x_13);
return x_15;
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
x_1 = l_Lean_Parser_errorAtSavedPos___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___elambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_checkNoImmediateColon___elambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 4);
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
x_9 = lean_ctor_get(x_4, 4);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_ctor_get(x_4, 3);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_22 = x_16;
} else {
 lean_dec_ref(x_16);
 x_22 = lean_box(0);
}
x_23 = lean_box(0);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_5, 0, x_24);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_19);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set(x_25, 4, x_5);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_ctor_get(x_4, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_4, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_4, 3);
lean_inc(x_30);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_31 = x_4;
} else {
 lean_dec_ref(x_4);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_33 = x_26;
} else {
 lean_dec_ref(x_26);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
if (lean_is_scalar(x_31)) {
 x_37 = lean_alloc_ctor(0, 5, 0);
} else {
 x_37 = x_31;
}
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set(x_37, 2, x_29);
lean_ctor_set(x_37, 3, x_30);
lean_ctor_set(x_37, 4, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_setExpectedFn___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_setExpectedFn(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_setExpectedFn___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_setExpected___elambda__1___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_setExpected___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_setExpected(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_pushNone___elambda__1___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind;
x_2 = l_Lean_Parser_instInhabitedInputContext___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___elambda__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_pushNone___elambda__1___rarg___closed__1;
x_3 = l_Lean_Parser_ParserState_pushSyntax(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___elambda__1(lean_object* x_1) {
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
x_1 = l_Lean_Parser_errorAtSavedPos___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___elambda__1___boxed(lean_object* x_1) {
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
lean_object* x_1; 
x_1 = lean_mk_string("antiquotNestedExpr");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_termParser___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_categoryParser___elambda__1), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_dbgTraceStateFn___closed__7;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_chFn___closed__1;
x_2 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__7;
x_2 = l_Lean_Parser_chFn___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_chFn___closed__1;
x_2 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__9;
x_2 = l_Lean_Parser_chFn___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__4;
x_6 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__8;
lean_inc(x_1);
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__2;
x_12 = l_Lean_Parser_ParserState_mkNode(x_7, x_11, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = l_Lean_Parser_decQuotDepth___closed__1;
x_14 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__5;
lean_inc(x_1);
x_15 = l_Lean_Parser_addQuotDepthFn(x_13, x_14, x_1, x_7);
x_16 = lean_ctor_get(x_15, 4);
lean_inc(x_16);
x_17 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_16, x_9);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__2;
x_19 = l_Lean_Parser_ParserState_mkNode(x_15, x_18, x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__6;
x_21 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__10;
x_22 = l_Lean_Parser_symbolFnAux(x_20, x_21, x_1, x_15);
x_23 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__2;
x_24 = l_Lean_Parser_ParserState_mkNode(x_22, x_23, x_4);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__4;
x_2 = l_Lean_Parser_symbolInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_termParser___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Parser_categoryParser(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__6;
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
x_1 = l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr___elambda__1(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("token_antiquot");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_tokenWithAntiquotFn___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquotFn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = l_Lean_Parser_tokenWithAntiquotFn___lambda__1___closed__2;
x_7 = l_Lean_Parser_ParserState_mkNode(x_2, x_6, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("%");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("$");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no space before");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_chFn___closed__1;
x_2 = l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__6;
x_2 = l_Lean_Parser_chFn___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_chFn___closed__1;
x_2 = l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__8;
x_2 = l_Lean_Parser_chFn___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquotFn___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__5;
x_8 = l_Lean_Parser_checkNoWsBeforeFn(x_7, x_2, x_1);
x_9 = lean_ctor_get(x_8, 4);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_dec(x_2);
x_12 = x_8;
goto block_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__2;
x_20 = l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__7;
lean_inc(x_2);
x_21 = l_Lean_Parser_symbolFnAux(x_19, x_20, x_2, x_8);
x_22 = lean_ctor_get(x_21, 4);
lean_inc(x_22);
x_23 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_22, x_10);
lean_dec(x_22);
if (x_23 == 0)
{
lean_dec(x_2);
x_12 = x_21;
goto block_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__4;
x_25 = l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__9;
lean_inc(x_2);
x_26 = l_Lean_Parser_symbolFnAux(x_24, x_25, x_2, x_21);
x_27 = lean_ctor_get(x_26, 4);
lean_inc(x_27);
x_28 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_27, x_10);
lean_dec(x_27);
if (x_28 == 0)
{
lean_dec(x_2);
x_12 = x_26;
goto block_18;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = l_Lean_Parser_checkNoWsBeforeFn(x_7, x_2, x_26);
x_30 = lean_ctor_get(x_29, 4);
lean_inc(x_30);
x_31 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_30, x_10);
lean_dec(x_30);
if (x_31 == 0)
{
lean_dec(x_2);
x_12 = x_29;
goto block_18;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_32 = l_Lean_Parser_identNoAntiquot___closed__2;
x_33 = l_Lean_Parser_antiquotNestedExpr___closed__7;
x_34 = 1;
x_35 = l_Lean_Parser_orelseFnCore(x_32, x_33, x_34, x_2, x_29);
x_12 = x_35;
goto block_18;
}
}
}
}
block_18:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 4);
lean_inc(x_13);
x_14 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_13, x_10);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Parser_ParserState_restore(x_12, x_5, x_6);
lean_dec(x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = l_Lean_Parser_tokenWithAntiquotFn___lambda__1(x_5, x_12, x_16);
lean_dec(x_5);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquotFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_2);
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 4);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Parser_tokenWithAntiquotFn___lambda__2(x_4, x_2, x_11);
return x_12;
}
else
{
lean_dec(x_2);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquotFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_tokenWithAntiquotFn___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquotFn), 3, 1);
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
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquotFn), 3, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_String_trim(x_1);
lean_inc(x_2);
x_3 = l_Lean_Parser_symbolInfo(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquotFn), 3, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_symbol(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeStringParser(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_String_trim(x_1);
lean_inc(x_2);
x_3 = l_Lean_Parser_symbolInfo(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquotFn), 3, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeStringParser___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_instCoeStringParser(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_String_trim(x_1);
lean_inc(x_3);
x_4 = l_Lean_Parser_nonReservedSymbolInfo(x_3, x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolFn), 3, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquotFn), 3, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_String_trim(x_1);
x_4 = l_String_trim(x_2);
lean_inc(x_4);
lean_inc(x_3);
x_5 = l_Lean_Parser_unicodeSymbolInfo(x_3, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFn___boxed), 4, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquotFn), 3, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_unicodeSymbol(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = l_Lean_Parser_maxPrec;
x_5 = l_Lean_Parser_checkPrecFn(x_4, x_2, x_3);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = l_Lean_Parser_maxPrec;
x_5 = l_Lean_Parser_checkPrecFn(x_4, x_2, x_3);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_6, x_7);
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
x_1 = lean_mk_string("antiquot");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_mkAntiquot___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("antiquotName");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_mkAntiquot___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no space before ':");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot___closed__6;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot___closed__7;
x_2 = l_Lean_Parser_symbolInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot___closed__7;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot___closed__9;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquotFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__4;
x_2 = l_Lean_Parser_symbolInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__4;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot___closed__12;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquotFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_mkAntiquot___closed__11;
x_2 = l_Lean_Parser_mkAntiquot___closed__13;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_mkAntiquot___closed__14;
x_3 = l_Lean_Parser_setExpected(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_mkAntiquot___closed__11;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkNoWsBefore___elambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_mkAntiquot___closed__17;
x_2 = l_Lean_Parser_mkAntiquot___closed__13;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot___closed__16;
x_2 = l_Lean_Parser_noFirstTokenInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot___closed__18;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_manyFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no space before spliced term");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot___closed__21;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkNoWsBefore___elambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_maxPrec;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_setLhsPrecFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__24() {
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
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__25() {
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
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_4 = l_Lean_Parser_mkAntiquot___closed__5;
x_5 = lean_string_append(x_4, x_1);
x_6 = l_Lean_Parser_chFn___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_String_trim(x_1);
x_9 = 0;
lean_inc(x_8);
x_10 = l_Lean_Parser_nonReservedSymbolInfo(x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolFn), 3, 1);
lean_closure_set(x_11, 0, x_8);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquotFn), 3, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = l_Lean_Parser_mkAntiquot___closed__8;
x_14 = l_Lean_Parser_andthenInfo(x_13, x_10);
x_15 = l_Lean_Parser_mkAntiquot___closed__10;
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_12);
x_17 = l_Lean_Parser_epsilonInfo;
x_18 = l_Lean_Parser_andthenInfo(x_17, x_14);
x_19 = lean_alloc_closure((void*)(l_Lean_Parser_checkNoWsBefore___elambda__1___boxed), 3, 1);
lean_closure_set(x_19, 0, x_7);
x_20 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_16);
x_21 = l_Lean_Parser_mkAntiquot___closed__4;
x_22 = l_Lean_Parser_nodeInfo(x_21, x_18);
x_23 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_20);
x_24 = l_Lean_Parser_antiquotExpr;
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = l_Lean_Parser_mkAntiquot___closed__15;
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_80; 
x_80 = lean_box(0);
x_28 = x_80;
goto block_79;
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_2, 0);
lean_inc(x_81);
lean_dec(x_2);
x_28 = x_81;
goto block_79;
}
block_79:
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Parser_mkAntiquot___closed__2;
x_30 = l_Lean_Name_append(x_28, x_29);
lean_dec(x_28);
if (x_3 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_31 = l_Lean_Parser_andthenInfo(x_25, x_22);
x_32 = l_Lean_Parser_antiquotExpr___closed__2;
x_33 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_33, 0, x_32);
lean_closure_set(x_33, 1, x_23);
x_34 = l_Lean_Parser_andthenInfo(x_17, x_31);
x_35 = l_Lean_Parser_mkAntiquot___closed__22;
x_36 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_36, 0, x_35);
lean_closure_set(x_36, 1, x_33);
x_37 = l_Lean_Parser_mkAntiquot___closed__19;
x_38 = l_Lean_Parser_andthenInfo(x_37, x_34);
x_39 = l_Lean_Parser_mkAntiquot___closed__20;
x_40 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_40, 0, x_39);
lean_closure_set(x_40, 1, x_36);
x_41 = l_Lean_Parser_mkAntiquot___closed__11;
x_42 = l_Lean_Parser_andthenInfo(x_41, x_38);
x_43 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_43, 0, x_27);
lean_closure_set(x_43, 1, x_40);
x_44 = lean_alloc_closure((void*)(l_Lean_Parser_atomicFn), 3, 1);
lean_closure_set(x_44, 0, x_43);
lean_inc(x_30);
x_45 = l_Lean_Parser_nodeInfo(x_30, x_42);
x_46 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_46, 0, x_30);
lean_closure_set(x_46, 1, x_44);
x_47 = l_Lean_Parser_andthenInfo(x_45, x_17);
x_48 = l_Lean_Parser_mkAntiquot___closed__23;
x_49 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_49, 0, x_46);
lean_closure_set(x_49, 1, x_48);
x_50 = l_Lean_Parser_andthenInfo(x_17, x_47);
x_51 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot___elambda__1), 3, 1);
lean_closure_set(x_51, 0, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_53 = l_Lean_Parser_mkAntiquot___closed__24;
x_54 = l_Lean_Parser_orelseInfo(x_22, x_53);
x_55 = l_Lean_Parser_mkAntiquot___closed__25;
x_56 = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn), 4, 2);
lean_closure_set(x_56, 0, x_23);
lean_closure_set(x_56, 1, x_55);
x_57 = l_Lean_Parser_andthenInfo(x_25, x_54);
x_58 = l_Lean_Parser_antiquotExpr___closed__2;
x_59 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_59, 0, x_58);
lean_closure_set(x_59, 1, x_56);
x_60 = l_Lean_Parser_andthenInfo(x_17, x_57);
x_61 = l_Lean_Parser_mkAntiquot___closed__22;
x_62 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_62, 0, x_61);
lean_closure_set(x_62, 1, x_59);
x_63 = l_Lean_Parser_mkAntiquot___closed__19;
x_64 = l_Lean_Parser_andthenInfo(x_63, x_60);
x_65 = l_Lean_Parser_mkAntiquot___closed__20;
x_66 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_66, 0, x_65);
lean_closure_set(x_66, 1, x_62);
x_67 = l_Lean_Parser_mkAntiquot___closed__11;
x_68 = l_Lean_Parser_andthenInfo(x_67, x_64);
x_69 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_69, 0, x_27);
lean_closure_set(x_69, 1, x_66);
x_70 = lean_alloc_closure((void*)(l_Lean_Parser_atomicFn), 3, 1);
lean_closure_set(x_70, 0, x_69);
lean_inc(x_30);
x_71 = l_Lean_Parser_nodeInfo(x_30, x_68);
x_72 = lean_alloc_closure((void*)(l_Lean_Parser_nodeFn), 4, 2);
lean_closure_set(x_72, 0, x_30);
lean_closure_set(x_72, 1, x_70);
x_73 = l_Lean_Parser_andthenInfo(x_71, x_17);
x_74 = l_Lean_Parser_mkAntiquot___closed__23;
x_75 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_75, 0, x_72);
lean_closure_set(x_75, 1, x_74);
x_76 = l_Lean_Parser_andthenInfo(x_17, x_73);
x_77 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot___elambda__2), 3, 1);
lean_closure_set(x_77, 0, x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT uint8_t l_Lean_Parser_tryAnti___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parser_peekToken(x_1, x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_5);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 2)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__3;
x_10 = lean_string_dec_eq(x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_7);
x_11 = 0;
return x_11;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_tryAnti(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_Parser_tryAnti___lambda__1(x_1, x_2, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tryAnti___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Parser_tryAnti___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tryAnti___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_tryAnti(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_withoutInfo___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_withoutInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_withoutInfo___elambda__1), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_errorAtSavedPos___closed__2;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = l_Lean_Parser_maxPrec;
x_5 = l_Lean_Parser_checkPrecFn(x_4, x_2, x_3);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_6, x_7);
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
lean_object* x_1; 
x_1 = lean_mk_string("antiquot_scope");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_mkAntiquotSplice___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__2;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquotSplice___closed__3;
x_2 = l_Lean_Parser_symbolInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquotSplice___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquotSplice___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquotFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquotSplice___closed__7;
x_2 = l_Lean_Parser_symbolInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquotSplice___closed__7;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquotSplice___closed__9;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquotFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_4 = l_Lean_Parser_mkAntiquotSplice___closed__2;
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
x_12 = l_Lean_Parser_mkAntiquotSplice___closed__8;
x_13 = l_Lean_Parser_andthenInfo(x_12, x_11);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = l_Lean_Parser_mkAntiquotSplice___closed__10;
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
x_17 = l_Lean_Parser_andthenInfo(x_8, x_13);
x_18 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_18, 0, x_10);
lean_closure_set(x_18, 1, x_16);
x_19 = l_Lean_Parser_mkAntiquotSplice___closed__4;
x_20 = l_Lean_Parser_andthenInfo(x_19, x_17);
x_21 = l_Lean_Parser_mkAntiquotSplice___closed__6;
x_22 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_18);
x_23 = l_Lean_Parser_epsilonInfo;
x_24 = l_Lean_Parser_andthenInfo(x_23, x_20);
x_25 = l_Lean_Parser_mkAntiquot___closed__22;
x_26 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_22);
x_27 = l_Lean_Parser_mkAntiquot___closed__19;
x_28 = l_Lean_Parser_andthenInfo(x_27, x_24);
x_29 = l_Lean_Parser_mkAntiquot___closed__20;
x_30 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_30, 0, x_29);
lean_closure_set(x_30, 1, x_26);
x_31 = l_Lean_Parser_mkAntiquot___closed__11;
x_32 = l_Lean_Parser_andthenInfo(x_31, x_28);
x_33 = l_Lean_Parser_mkAntiquot___closed__15;
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
x_39 = l_Lean_Parser_andthenInfo(x_37, x_23);
x_40 = l_Lean_Parser_mkAntiquot___closed__23;
x_41 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_41, 0, x_38);
lean_closure_set(x_41, 1, x_40);
x_42 = l_Lean_Parser_andthenInfo(x_23, x_39);
x_43 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquotSplice___elambda__1), 3, 1);
lean_closure_set(x_43, 0, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_mkAntiquotSplice(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("antiquot_suffix_splice");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_apply_2(x_2, x_3, x_1);
x_10 = lean_ctor_get(x_9, 4);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_4);
x_6 = lean_apply_2(x_2, x_4, x_5);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_4, 4);
lean_inc(x_10);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
x_14 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_13);
lean_dec(x_13);
x_15 = l_Lean_Syntax_isAntiquot(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__2(x_6, x_3, x_4, x_1, x_16);
lean_dec(x_1);
return x_17;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSuffixSpliceFn), 5, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSuffixSpliceFn), 5, 3);
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
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_1; 
x_1 = lean_mk_string("sepBy");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_sepByElemParser___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_sepByElemParser___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_sepByElemParser___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("*");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = l_String_trim(x_2);
x_4 = l_Lean_Parser_sepByElemParser___closed__3;
x_5 = lean_string_append(x_3, x_4);
x_6 = l_String_trim(x_5);
lean_dec(x_5);
lean_inc(x_6);
x_7 = l_Lean_Parser_symbolInfo(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn___boxed), 3, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquotFn), 3, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Parser_sepByElemParser___closed__2;
x_12 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_11, x_1, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_sepByElemParser(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy___elambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_sepByFn(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Parser_sepBy___elambda__1(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1___elambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_sepBy1Fn(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Parser_sepBy1___elambda__1(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserOfStackFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = l_Lean_Parser_categoryParserOfStackFn___closed__1;
x_17 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_16, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_18 = lean_box(0);
x_19 = l_Lean_Parser_categoryParserOfStackFn___closed__2;
x_20 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_19, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserOfStackFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_categoryParserOfStackFn(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserOfStack___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 2);
lean_dec(x_6);
lean_ctor_set(x_3, 2, x_2);
x_7 = l_Lean_Parser_categoryParserOfStackFn(x_1, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 3);
x_11 = lean_ctor_get(x_3, 4);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_ctor_get(x_3, 6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_2);
lean_ctor_set(x_15, 3, x_10);
lean_ctor_set(x_15, 4, x_11);
lean_ctor_set(x_15, 5, x_13);
lean_ctor_set(x_15, 6, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*7, x_12);
x_16 = l_Lean_Parser_categoryParserOfStackFn(x_1, x_15, x_4);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserOfStack(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserOfStack___elambda__1___boxed), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = l_Lean_Parser_errorAtSavedPos___closed__2;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserOfStack___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_categoryParserOfStack___elambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_evalParserConstUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_evalParserConstUnsafe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_evalParserConstUnsafe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_evalParserConstUnsafe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_evalParserConstUnsafe___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_evalParserConstUnsafe___closed__2;
x_2 = l_Lean_Parser_evalParserConstUnsafe___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_evalParserConstUnsafe___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_evalParserConstUnsafe___closed__4;
x_2 = l_Lean_Parser_evalParserConstUnsafe___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_evalParserConstUnsafe___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TrailingParser");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_evalParserConstUnsafe___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_evalParserConstUnsafe___closed__4;
x_2 = l_Lean_Parser_evalParserConstUnsafe___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_evalParserConstUnsafe___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("error running parser ");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_evalParserConstUnsafe___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(": ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = l_Lean_Parser_evalParserConstUnsafe___closed__5;
lean_inc(x_1);
lean_inc(x_5);
x_8 = l_Lean_Environment_evalConstCheck___rarg(x_5, x_6, x_7, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_8);
x_9 = l_Lean_Parser_evalParserConstUnsafe___closed__7;
lean_inc(x_1);
x_10 = l_Lean_Environment_evalConstCheck___rarg(x_5, x_6, x_9, x_1);
lean_dec(x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = 1;
x_13 = l_Lean_Name_toString(x_1, x_12);
x_14 = l_Lean_Parser_evalParserConstUnsafe___closed__8;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Lean_Parser_evalParserConstUnsafe___closed__9;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_11);
lean_dec(x_11);
x_19 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_box(0);
x_22 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_20, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_apply_2(x_24, x_2, x_3);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_26 = lean_ctor_get(x_8, 0);
lean_inc(x_26);
lean_dec(x_8);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_apply_2(x_27, x_2, x_3);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConst___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConst___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConst___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_evalParserConst___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConst___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_evalParserConst(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFnUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_2);
x_15 = 1;
x_16 = l_Lean_Name_toString(x_13, x_15);
x_17 = l_Lean_Parser_parserOfStackFnUnsafe___closed__2;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_box(0);
x_22 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_20, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_13);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Parser_evalParserConstUnsafe(x_26, x_2, x_3);
x_28 = lean_ctor_get(x_27, 4);
lean_inc(x_28);
x_29 = lean_box(0);
x_30 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_dec(x_5);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
x_32 = lean_array_get_size(x_31);
lean_dec(x_31);
x_33 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
x_34 = lean_nat_dec_eq(x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_box(0);
x_36 = l_Lean_Parser_parserOfStackFnUnsafe___closed__3;
x_37 = l_Lean_Parser_ParserState_mkUnexpectedError(x_27, x_36, x_35);
return x_37;
}
else
{
return x_27;
}
}
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_2);
x_38 = 1;
x_39 = l_Lean_Name_toString(x_13, x_38);
x_40 = l_Lean_Parser_parserOfStackFnUnsafe___closed__4;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_box(0);
x_45 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_43, x_44);
return x_45;
}
}
else
{
lean_object* x_46; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_2);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
lean_dec(x_14);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = 1;
x_48 = l_Lean_Name_toString(x_13, x_47);
x_49 = l_Lean_Parser_parserOfStackFnUnsafe___closed__2;
x_50 = lean_string_append(x_49, x_48);
lean_dec(x_48);
x_51 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_box(0);
x_54 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_52, x_53);
return x_54;
}
else
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_46);
x_55 = 1;
x_56 = l_Lean_Name_toString(x_13, x_55);
x_57 = l_Lean_Parser_parserOfStackFnUnsafe___closed__4;
x_58 = lean_string_append(x_57, x_56);
lean_dec(x_56);
x_59 = l_Lean_Parser_instInhabitedInputContext___closed__2;
x_60 = lean_string_append(x_58, x_59);
x_61 = lean_box(0);
x_62 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_60, x_61);
return x_62;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_2);
x_63 = lean_box(0);
x_64 = l_Lean_Parser_parserOfStackFnUnsafe___closed__1;
x_65 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_64, x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_66 = lean_box(0);
x_67 = l_Lean_Parser_parserOfStackFnUnsafe___closed__5;
x_68 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_67, x_66);
return x_68;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFnUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_parserOfStackFnUnsafe(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_parserOfStackFn___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_parserOfStackFn(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 2);
lean_dec(x_6);
lean_ctor_set(x_3, 2, x_2);
x_7 = l_Lean_Parser_parserOfStackFnUnsafe(x_1, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 3);
x_11 = lean_ctor_get(x_3, 4);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_ctor_get(x_3, 6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_2);
lean_ctor_set(x_15, 3, x_10);
lean_ctor_set(x_15, 4, x_11);
lean_ctor_set(x_15, 5, x_13);
lean_ctor_set(x_15, 6, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*7, x_12);
x_16 = l_Lean_Parser_parserOfStackFnUnsafe(x_1, x_15, x_4);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStack___elambda__1___boxed), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = l_Lean_Parser_errorAtSavedPos___closed__2;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_parserOfStack___elambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("internal");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parseQuotWithCurrentStage");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__2;
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(Lean bootstrapping) use parsers from the current stage inside quotations");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__1;
x_3 = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__5;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__4;
x_3 = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__6;
x_4 = l_Lean_Option_register___at_Std_Format_initFn____x40_Lean_Data_Format___hyg_48____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_internal_parseQuotWithCurrentStage___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 4);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_2(x_8, x_3, x_4);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = l_Lean_Parser_internal_parseQuotWithCurrentStage;
x_14 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_apply_2(x_15, x_3, x_4);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
lean_inc(x_1);
x_18 = l_Lean_Environment_contains(x_17, x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_apply_2(x_19, x_3, x_4);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_2);
x_21 = l_Lean_Parser_evalParserConstUnsafe(x_1, x_3, x_4);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_apply_2(x_22, x_3, x_4);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = l_Lean_Parser_longestMatchFn(x_6, x_1, x_2, x_3);
x_8 = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_List_appendTR___rarg(x_8, x_2);
x_10 = l_List_isEmpty___rarg(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = l_Lean_Parser_leadingParserAux___lambda__1(x_9, x_3, x_4, x_5, x_11);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_13 = 1;
x_14 = l_Lean_Name_toString(x_6, x_13);
x_15 = l_Lean_Parser_ParserState_mkError(x_4, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_12 = lean_ctor_get(x_10, 4);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_Parser_leadingParserAux___lambda__2(x_2, x_11, x_4, x_10, x_7, x_1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_leadingParserAux___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_leadingParserAux___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Parser_leadingParserAux(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Parser_leadingParser(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoopStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_List_appendTR___rarg(x_3, x_7);
x_9 = l_Lean_Parser_longestMatchFn(x_6, x_8, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_trailingLoop(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_8);
lean_dec(x_8);
x_10 = l_Lean_Parser_ParserState_popSyntax(x_1);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_2);
x_11 = l_Lean_Parser_trailingLoopStep(x_2, x_9, x_3, x_4, x_10);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_ctor_get(x_11, 2);
lean_inc(x_15);
x_16 = lean_nat_dec_eq(x_15, x_5);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_9);
lean_dec(x_5);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_6, x_17);
x_19 = l_Lean_Parser_ParserState_restore(x_11, x_18, x_5);
lean_dec(x_18);
x_20 = l_Lean_Parser_ParserState_pushSyntax(x_19, x_9);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_9);
lean_dec(x_5);
x_21 = l_Lean_Parser_trailingLoop(x_2, x_4, x_11);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
lean_dec(x_7);
x_8 = l_List_isEmpty___rarg(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Parser_trailingLoop___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
x_12 = l_List_isEmpty___rarg(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Parser_trailingLoop___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_13);
return x_14;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = 0;
lean_inc(x_2);
x_9 = l_Lean_Parser_indexed___rarg(x_7, x_2, x_3, x_8);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 4);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Parser_ParserState_restore(x_10, x_5, x_6);
lean_dec(x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Lean_Parser_trailingLoop___lambda__3(x_10, x_1, x_11, x_2, x_6, x_5, x_16);
lean_dec(x_5);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_trailingLoop___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_trailingLoop___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_trailingLoop___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
x_13 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_12, x_10);
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
x_17 = lean_ctor_get(x_16, 4);
lean_inc(x_17);
x_18 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_677____at_Lean_Parser_ParserState_hasError___spec__1(x_17, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdxFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_array_get_size(x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_string_utf8_get(x_7, x_5);
x_9 = l_Char_isDigit(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_11 = l_Lean_Parser_fieldIdxFn___closed__1;
x_12 = l_Lean_Parser_ParserState_mkErrorAt(x_2, x_11, x_5, x_10);
return x_12;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 48;
x_14 = x_8 == x_13;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_15 = l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1;
x_16 = l_Lean_Parser_takeWhileFn(x_15, x_1, x_2);
x_17 = l_Lean_fieldIdxKind;
x_18 = l_Lean_Parser_mkNodeToken(x_17, x_5, x_1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_4);
x_20 = l_Lean_Parser_fieldIdxFn___closed__1;
x_21 = l_Lean_Parser_ParserState_mkErrorAt(x_2, x_20, x_5, x_19);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdxFn___boxed(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_1; 
x_1 = lean_mk_string("fieldIdx");
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_fieldIdx___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_fieldIdx___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_fieldIdx___closed__1;
x_2 = l_Lean_Parser_fieldIdx___closed__3;
x_3 = 1;
x_4 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_fieldIdx___closed__1;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_fieldIdx___closed__4;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Parser_fieldIdx___closed__5;
x_4 = l_Lean_Parser_orelseInfo(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_fieldIdxFn___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_fieldIdx___closed__4;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lean_Parser_fieldIdx___closed__7;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotFn), 4, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_fieldIdx___closed__6;
x_2 = l_Lean_Parser_fieldIdx___closed__8;
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
x_1 = l_Lean_Parser_fieldIdx___closed__9;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = x_1 + x_7;
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = l_Lean_Syntax_getArgs(x_2);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_foldArgsM___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_foldArgs___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = x_1 + x_7;
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___at_Lean_Syntax_forArgsM___spec__2___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = x_1 + x_7;
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___at_Lean_Syntax_forArgsM___spec__2___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___at_Lean_Syntax_forArgsM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_4 == x_5;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_1);
x_10 = lean_apply_1(x_1, x_9);
x_11 = lean_box_usize(x_4);
x_12 = lean_box_usize(x_5);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___at_Lean_Syntax_forArgsM___spec__2___rarg___lambda__1___boxed), 6, 5);
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
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___at_Lean_Syntax_forArgsM___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___at_Lean_Syntax_forArgsM___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l_Lean_Syntax_getArgs(x_2);
lean_dec(x_2);
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
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___at_Lean_Syntax_forArgsM___spec__2___rarg(x_3, x_1, x_4, x_17, x_18, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_forArgsM___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___at_Lean_Syntax_forArgsM___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___at_Lean_Syntax_forArgsM___spec__2___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___at_Lean_Syntax_forArgsM___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__1___at_Lean_Syntax_forArgsM___spec__2___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
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
LEAN_EXPORT lean_object* initialize_Lean_Parser_Basic(lean_object* w) {
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
l_Lean_Parser_argPrec = _init_l_Lean_Parser_argPrec();
lean_mark_persistent(l_Lean_Parser_argPrec);
l_Lean_Parser_leadPrec = _init_l_Lean_Parser_leadPrec();
lean_mark_persistent(l_Lean_Parser_leadPrec);
l_Lean_Parser_minPrec = _init_l_Lean_Parser_minPrec();
lean_mark_persistent(l_Lean_Parser_minPrec);
l_Lean_Parser_TokenCacheEntry_startPos___default = _init_l_Lean_Parser_TokenCacheEntry_startPos___default();
lean_mark_persistent(l_Lean_Parser_TokenCacheEntry_startPos___default);
l_Lean_Parser_TokenCacheEntry_stopPos___default = _init_l_Lean_Parser_TokenCacheEntry_stopPos___default();
lean_mark_persistent(l_Lean_Parser_TokenCacheEntry_stopPos___default);
l_Lean_Parser_TokenCacheEntry_token___default = _init_l_Lean_Parser_TokenCacheEntry_token___default();
lean_mark_persistent(l_Lean_Parser_TokenCacheEntry_token___default);
l_Lean_Parser_instInhabitedInputContext___closed__1 = _init_l_Lean_Parser_instInhabitedInputContext___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext___closed__1);
l_Lean_Parser_instInhabitedInputContext___closed__2 = _init_l_Lean_Parser_instInhabitedInputContext___closed__2();
lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext___closed__2);
l_Lean_Parser_instInhabitedInputContext___closed__3 = _init_l_Lean_Parser_instInhabitedInputContext___closed__3();
lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext___closed__3);
l_Lean_Parser_instInhabitedInputContext___closed__4 = _init_l_Lean_Parser_instInhabitedInputContext___closed__4();
lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext___closed__4);
l_Lean_Parser_instInhabitedInputContext = _init_l_Lean_Parser_instInhabitedInputContext();
lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext);
l_Lean_Parser_ParserModuleContext_currNamespace___default = _init_l_Lean_Parser_ParserModuleContext_currNamespace___default();
lean_mark_persistent(l_Lean_Parser_ParserModuleContext_currNamespace___default);
l_Lean_Parser_ParserModuleContext_openDecls___default = _init_l_Lean_Parser_ParserModuleContext_openDecls___default();
lean_mark_persistent(l_Lean_Parser_ParserModuleContext_openDecls___default);
l_Lean_Parser_ParserContext_quotDepth___default = _init_l_Lean_Parser_ParserContext_quotDepth___default();
lean_mark_persistent(l_Lean_Parser_ParserContext_quotDepth___default);
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
l_Lean_Parser_instBEqError___closed__1 = _init_l_Lean_Parser_instBEqError___closed__1();
lean_mark_persistent(l_Lean_Parser_instBEqError___closed__1);
l_Lean_Parser_instBEqError = _init_l_Lean_Parser_instBEqError();
lean_mark_persistent(l_Lean_Parser_instBEqError);
l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString___closed__1 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString___closed__1);
l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString___closed__2 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_Error_expectedToString___closed__2);
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
l_Lean_Parser_ParserState_stxStack___default = _init_l_Lean_Parser_ParserState_stxStack___default();
lean_mark_persistent(l_Lean_Parser_ParserState_stxStack___default);
l_Lean_Parser_ParserState_lhsPrec___default = _init_l_Lean_Parser_ParserState_lhsPrec___default();
lean_mark_persistent(l_Lean_Parser_ParserState_lhsPrec___default);
l_Lean_Parser_ParserState_pos___default = _init_l_Lean_Parser_ParserState_pos___default();
lean_mark_persistent(l_Lean_Parser_ParserState_pos___default);
l_Lean_Parser_ParserState_errorMsg___default = _init_l_Lean_Parser_ParserState_errorMsg___default();
lean_mark_persistent(l_Lean_Parser_ParserState_errorMsg___default);
l_Lean_Parser_ParserState_mkEOIError___closed__1 = _init_l_Lean_Parser_ParserState_mkEOIError___closed__1();
lean_mark_persistent(l_Lean_Parser_ParserState_mkEOIError___closed__1);
l_Lean_Parser_instInhabitedFirstTokens = _init_l_Lean_Parser_instInhabitedFirstTokens();
lean_mark_persistent(l_Lean_Parser_instInhabitedFirstTokens);
l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__1 = _init_l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__1();
lean_mark_persistent(l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__1);
l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__2 = _init_l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__2();
lean_mark_persistent(l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__2);
l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__3 = _init_l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__3();
lean_mark_persistent(l_List_toString___at_Lean_Parser_FirstTokens_toStr___spec__1___closed__3);
l_Lean_Parser_FirstTokens_toStr___closed__1 = _init_l_Lean_Parser_FirstTokens_toStr___closed__1();
lean_mark_persistent(l_Lean_Parser_FirstTokens_toStr___closed__1);
l_Lean_Parser_FirstTokens_toStr___closed__2 = _init_l_Lean_Parser_FirstTokens_toStr___closed__2();
lean_mark_persistent(l_Lean_Parser_FirstTokens_toStr___closed__2);
l_Lean_Parser_FirstTokens_toStr___closed__3 = _init_l_Lean_Parser_FirstTokens_toStr___closed__3();
lean_mark_persistent(l_Lean_Parser_FirstTokens_toStr___closed__3);
l_Lean_Parser_FirstTokens_instToStringFirstTokens___closed__1 = _init_l_Lean_Parser_FirstTokens_instToStringFirstTokens___closed__1();
lean_mark_persistent(l_Lean_Parser_FirstTokens_instToStringFirstTokens___closed__1);
l_Lean_Parser_FirstTokens_instToStringFirstTokens = _init_l_Lean_Parser_FirstTokens_instToStringFirstTokens();
lean_mark_persistent(l_Lean_Parser_FirstTokens_instToStringFirstTokens);
l_Lean_Parser_ParserInfo_firstTokens___default = _init_l_Lean_Parser_ParserInfo_firstTokens___default();
lean_mark_persistent(l_Lean_Parser_ParserInfo_firstTokens___default);
l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__1 = _init_l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__1);
l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__2 = _init_l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__2);
l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__3 = _init_l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserInfo___lambda__2___closed__3);
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
l_Lean_Parser_dbgTraceStateFn___closed__1 = _init_l_Lean_Parser_dbgTraceStateFn___closed__1();
lean_mark_persistent(l_Lean_Parser_dbgTraceStateFn___closed__1);
l_Lean_Parser_dbgTraceStateFn___closed__2 = _init_l_Lean_Parser_dbgTraceStateFn___closed__2();
lean_mark_persistent(l_Lean_Parser_dbgTraceStateFn___closed__2);
l_Lean_Parser_dbgTraceStateFn___closed__3 = _init_l_Lean_Parser_dbgTraceStateFn___closed__3();
lean_mark_persistent(l_Lean_Parser_dbgTraceStateFn___closed__3);
l_Lean_Parser_dbgTraceStateFn___closed__4 = _init_l_Lean_Parser_dbgTraceStateFn___closed__4();
lean_mark_persistent(l_Lean_Parser_dbgTraceStateFn___closed__4);
l_Lean_Parser_dbgTraceStateFn___closed__5 = _init_l_Lean_Parser_dbgTraceStateFn___closed__5();
lean_mark_persistent(l_Lean_Parser_dbgTraceStateFn___closed__5);
l_Lean_Parser_dbgTraceStateFn___closed__6 = _init_l_Lean_Parser_dbgTraceStateFn___closed__6();
lean_mark_persistent(l_Lean_Parser_dbgTraceStateFn___closed__6);
l_Lean_Parser_dbgTraceStateFn___closed__7 = _init_l_Lean_Parser_dbgTraceStateFn___closed__7();
lean_mark_persistent(l_Lean_Parser_dbgTraceStateFn___closed__7);
l_Lean_Parser_epsilonInfo___closed__1 = _init_l_Lean_Parser_epsilonInfo___closed__1();
lean_mark_persistent(l_Lean_Parser_epsilonInfo___closed__1);
l_Lean_Parser_epsilonInfo___closed__2 = _init_l_Lean_Parser_epsilonInfo___closed__2();
lean_mark_persistent(l_Lean_Parser_epsilonInfo___closed__2);
l_Lean_Parser_epsilonInfo___closed__3 = _init_l_Lean_Parser_epsilonInfo___closed__3();
lean_mark_persistent(l_Lean_Parser_epsilonInfo___closed__3);
l_Lean_Parser_epsilonInfo = _init_l_Lean_Parser_epsilonInfo();
lean_mark_persistent(l_Lean_Parser_epsilonInfo);
l_Lean_Parser_errorAtSavedPos___closed__1 = _init_l_Lean_Parser_errorAtSavedPos___closed__1();
lean_mark_persistent(l_Lean_Parser_errorAtSavedPos___closed__1);
l_Lean_Parser_errorAtSavedPos___closed__2 = _init_l_Lean_Parser_errorAtSavedPos___closed__2();
lean_mark_persistent(l_Lean_Parser_errorAtSavedPos___closed__2);
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
l_Lean_Parser_incQuotDepth___closed__1 = _init_l_Lean_Parser_incQuotDepth___closed__1();
lean_mark_persistent(l_Lean_Parser_incQuotDepth___closed__1);
l_Lean_Parser_decQuotDepth___closed__1 = _init_l_Lean_Parser_decQuotDepth___closed__1();
lean_mark_persistent(l_Lean_Parser_decQuotDepth___closed__1);
l_Lean_Parser_notFollowedByFn___closed__1 = _init_l_Lean_Parser_notFollowedByFn___closed__1();
lean_mark_persistent(l_Lean_Parser_notFollowedByFn___closed__1);
l_Lean_Parser_manyAux___lambda__3___closed__1 = _init_l_Lean_Parser_manyAux___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Parser_manyAux___lambda__3___closed__1);
l_Lean_Parser_many1Unbox___closed__1 = _init_l_Lean_Parser_many1Unbox___closed__1();
lean_mark_persistent(l_Lean_Parser_many1Unbox___closed__1);
l_Lean_Parser_finishCommentBlock_eoi___closed__1 = _init_l_Lean_Parser_finishCommentBlock_eoi___closed__1();
lean_mark_persistent(l_Lean_Parser_finishCommentBlock_eoi___closed__1);
l_Lean_Parser_whitespace___closed__1 = _init_l_Lean_Parser_whitespace___closed__1();
lean_mark_persistent(l_Lean_Parser_whitespace___closed__1);
l_Lean_Parser_whitespace___closed__2 = _init_l_Lean_Parser_whitespace___closed__2();
lean_mark_persistent(l_Lean_Parser_whitespace___closed__2);
l_Lean_Parser_chFn___closed__1 = _init_l_Lean_Parser_chFn___closed__1();
lean_mark_persistent(l_Lean_Parser_chFn___closed__1);
l_Lean_Parser_hexDigitFn___closed__1 = _init_l_Lean_Parser_hexDigitFn___closed__1();
lean_mark_persistent(l_Lean_Parser_hexDigitFn___closed__1);
l_Lean_Parser_quotedCharCoreFn___closed__1 = _init_l_Lean_Parser_quotedCharCoreFn___closed__1();
lean_mark_persistent(l_Lean_Parser_quotedCharCoreFn___closed__1);
l_Lean_Parser_quotedCharFn___closed__1 = _init_l_Lean_Parser_quotedCharFn___closed__1();
lean_mark_persistent(l_Lean_Parser_quotedCharFn___closed__1);
l_Lean_Parser_charLitFnAux___closed__1 = _init_l_Lean_Parser_charLitFnAux___closed__1();
lean_mark_persistent(l_Lean_Parser_charLitFnAux___closed__1);
l_Lean_Parser_strLitFnAux___closed__1 = _init_l_Lean_Parser_strLitFnAux___closed__1();
lean_mark_persistent(l_Lean_Parser_strLitFnAux___closed__1);
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
l_Lean_Parser_identFnAux_parse___lambda__2___closed__1 = _init_l_Lean_Parser_identFnAux_parse___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Parser_identFnAux_parse___lambda__2___closed__1);
l_Lean_Parser_identFnAux_parse___lambda__2___closed__2 = _init_l_Lean_Parser_identFnAux_parse___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Parser_identFnAux_parse___lambda__2___closed__2);
l_Lean_Parser_identFnAux_parse___lambda__2___closed__3 = _init_l_Lean_Parser_identFnAux_parse___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Parser_identFnAux_parse___lambda__2___closed__3);
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
l_Lean_Parser_nonReservedSymbolInfo___closed__4 = _init_l_Lean_Parser_nonReservedSymbolInfo___closed__4();
lean_mark_persistent(l_Lean_Parser_nonReservedSymbolInfo___closed__4);
l_Lean_Parser_unicodeSymbolInfo___closed__1 = _init_l_Lean_Parser_unicodeSymbolInfo___closed__1();
lean_mark_persistent(l_Lean_Parser_unicodeSymbolInfo___closed__1);
l_Lean_Parser_unicodeSymbolFn___closed__1 = _init_l_Lean_Parser_unicodeSymbolFn___closed__1();
lean_mark_persistent(l_Lean_Parser_unicodeSymbolFn___closed__1);
l_Lean_Parser_mkAtomicInfo___closed__1 = _init_l_Lean_Parser_mkAtomicInfo___closed__1();
lean_mark_persistent(l_Lean_Parser_mkAtomicInfo___closed__1);
l_Lean_Parser_mkAtomicInfo___closed__2 = _init_l_Lean_Parser_mkAtomicInfo___closed__2();
lean_mark_persistent(l_Lean_Parser_mkAtomicInfo___closed__2);
l_Lean_Parser_numLitFn___closed__1 = _init_l_Lean_Parser_numLitFn___closed__1();
lean_mark_persistent(l_Lean_Parser_numLitFn___closed__1);
l_Lean_Parser_numLitNoAntiquot___closed__1 = _init_l_Lean_Parser_numLitNoAntiquot___closed__1();
lean_mark_persistent(l_Lean_Parser_numLitNoAntiquot___closed__1);
l_Lean_Parser_numLitNoAntiquot___closed__2 = _init_l_Lean_Parser_numLitNoAntiquot___closed__2();
lean_mark_persistent(l_Lean_Parser_numLitNoAntiquot___closed__2);
l_Lean_Parser_numLitNoAntiquot___closed__3 = _init_l_Lean_Parser_numLitNoAntiquot___closed__3();
lean_mark_persistent(l_Lean_Parser_numLitNoAntiquot___closed__3);
l_Lean_Parser_numLitNoAntiquot___closed__4 = _init_l_Lean_Parser_numLitNoAntiquot___closed__4();
lean_mark_persistent(l_Lean_Parser_numLitNoAntiquot___closed__4);
l_Lean_Parser_numLitNoAntiquot = _init_l_Lean_Parser_numLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_numLitNoAntiquot);
l_Lean_Parser_scientificLitFn___closed__1 = _init_l_Lean_Parser_scientificLitFn___closed__1();
lean_mark_persistent(l_Lean_Parser_scientificLitFn___closed__1);
l_Lean_Parser_scientificLitFn___closed__2 = _init_l_Lean_Parser_scientificLitFn___closed__2();
lean_mark_persistent(l_Lean_Parser_scientificLitFn___closed__2);
l_Lean_Parser_scientificLitNoAntiquot___closed__1 = _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1();
lean_mark_persistent(l_Lean_Parser_scientificLitNoAntiquot___closed__1);
l_Lean_Parser_scientificLitNoAntiquot___closed__2 = _init_l_Lean_Parser_scientificLitNoAntiquot___closed__2();
lean_mark_persistent(l_Lean_Parser_scientificLitNoAntiquot___closed__2);
l_Lean_Parser_scientificLitNoAntiquot___closed__3 = _init_l_Lean_Parser_scientificLitNoAntiquot___closed__3();
lean_mark_persistent(l_Lean_Parser_scientificLitNoAntiquot___closed__3);
l_Lean_Parser_scientificLitNoAntiquot___closed__4 = _init_l_Lean_Parser_scientificLitNoAntiquot___closed__4();
lean_mark_persistent(l_Lean_Parser_scientificLitNoAntiquot___closed__4);
l_Lean_Parser_scientificLitNoAntiquot = _init_l_Lean_Parser_scientificLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_scientificLitNoAntiquot);
l_Lean_Parser_strLitFn___closed__1 = _init_l_Lean_Parser_strLitFn___closed__1();
lean_mark_persistent(l_Lean_Parser_strLitFn___closed__1);
l_Lean_Parser_strLitFn___closed__2 = _init_l_Lean_Parser_strLitFn___closed__2();
lean_mark_persistent(l_Lean_Parser_strLitFn___closed__2);
l_Lean_Parser_strLitNoAntiquot___closed__1 = _init_l_Lean_Parser_strLitNoAntiquot___closed__1();
lean_mark_persistent(l_Lean_Parser_strLitNoAntiquot___closed__1);
l_Lean_Parser_strLitNoAntiquot___closed__2 = _init_l_Lean_Parser_strLitNoAntiquot___closed__2();
lean_mark_persistent(l_Lean_Parser_strLitNoAntiquot___closed__2);
l_Lean_Parser_strLitNoAntiquot___closed__3 = _init_l_Lean_Parser_strLitNoAntiquot___closed__3();
lean_mark_persistent(l_Lean_Parser_strLitNoAntiquot___closed__3);
l_Lean_Parser_strLitNoAntiquot___closed__4 = _init_l_Lean_Parser_strLitNoAntiquot___closed__4();
lean_mark_persistent(l_Lean_Parser_strLitNoAntiquot___closed__4);
l_Lean_Parser_strLitNoAntiquot = _init_l_Lean_Parser_strLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_strLitNoAntiquot);
l_Lean_Parser_charLitFn___closed__1 = _init_l_Lean_Parser_charLitFn___closed__1();
lean_mark_persistent(l_Lean_Parser_charLitFn___closed__1);
l_Lean_Parser_charLitFn___closed__2 = _init_l_Lean_Parser_charLitFn___closed__2();
lean_mark_persistent(l_Lean_Parser_charLitFn___closed__2);
l_Lean_Parser_charLitFn___closed__3 = _init_l_Lean_Parser_charLitFn___closed__3();
lean_mark_persistent(l_Lean_Parser_charLitFn___closed__3);
l_Lean_Parser_charLitNoAntiquot___closed__1 = _init_l_Lean_Parser_charLitNoAntiquot___closed__1();
lean_mark_persistent(l_Lean_Parser_charLitNoAntiquot___closed__1);
l_Lean_Parser_charLitNoAntiquot___closed__2 = _init_l_Lean_Parser_charLitNoAntiquot___closed__2();
lean_mark_persistent(l_Lean_Parser_charLitNoAntiquot___closed__2);
l_Lean_Parser_charLitNoAntiquot___closed__3 = _init_l_Lean_Parser_charLitNoAntiquot___closed__3();
lean_mark_persistent(l_Lean_Parser_charLitNoAntiquot___closed__3);
l_Lean_Parser_charLitNoAntiquot___closed__4 = _init_l_Lean_Parser_charLitNoAntiquot___closed__4();
lean_mark_persistent(l_Lean_Parser_charLitNoAntiquot___closed__4);
l_Lean_Parser_charLitNoAntiquot = _init_l_Lean_Parser_charLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_charLitNoAntiquot);
l_Lean_Parser_nameLitFn___closed__1 = _init_l_Lean_Parser_nameLitFn___closed__1();
lean_mark_persistent(l_Lean_Parser_nameLitFn___closed__1);
l_Lean_Parser_nameLitFn___closed__2 = _init_l_Lean_Parser_nameLitFn___closed__2();
lean_mark_persistent(l_Lean_Parser_nameLitFn___closed__2);
l_Lean_Parser_nameLitNoAntiquot___closed__1 = _init_l_Lean_Parser_nameLitNoAntiquot___closed__1();
lean_mark_persistent(l_Lean_Parser_nameLitNoAntiquot___closed__1);
l_Lean_Parser_nameLitNoAntiquot___closed__2 = _init_l_Lean_Parser_nameLitNoAntiquot___closed__2();
lean_mark_persistent(l_Lean_Parser_nameLitNoAntiquot___closed__2);
l_Lean_Parser_nameLitNoAntiquot___closed__3 = _init_l_Lean_Parser_nameLitNoAntiquot___closed__3();
lean_mark_persistent(l_Lean_Parser_nameLitNoAntiquot___closed__3);
l_Lean_Parser_nameLitNoAntiquot___closed__4 = _init_l_Lean_Parser_nameLitNoAntiquot___closed__4();
lean_mark_persistent(l_Lean_Parser_nameLitNoAntiquot___closed__4);
l_Lean_Parser_nameLitNoAntiquot = _init_l_Lean_Parser_nameLitNoAntiquot();
lean_mark_persistent(l_Lean_Parser_nameLitNoAntiquot);
l_Lean_Parser_identFn___closed__1 = _init_l_Lean_Parser_identFn___closed__1();
lean_mark_persistent(l_Lean_Parser_identFn___closed__1);
l_Lean_Parser_identFn___closed__2 = _init_l_Lean_Parser_identFn___closed__2();
lean_mark_persistent(l_Lean_Parser_identFn___closed__2);
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
l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg___closed__1 = _init_l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg___closed__1);
l_Lean_Parser_instInhabitedLeadingIdentBehavior = _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior();
l_Lean_Parser_instBEqLeadingIdentBehavior___closed__1 = _init_l_Lean_Parser_instBEqLeadingIdentBehavior___closed__1();
lean_mark_persistent(l_Lean_Parser_instBEqLeadingIdentBehavior___closed__1);
l_Lean_Parser_instBEqLeadingIdentBehavior = _init_l_Lean_Parser_instBEqLeadingIdentBehavior();
lean_mark_persistent(l_Lean_Parser_instBEqLeadingIdentBehavior);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__1 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__1();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__1);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__2 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__2();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__2);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__3 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__3();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__3);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__4 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__4();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__4);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__5 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__5();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__5);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__6 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__6();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__6);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__7 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__7();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__7);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__8 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__8();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__8);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__9 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__9();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__9);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__10 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__10();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__10);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__11 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__11();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__11);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__12 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__12();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__12);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__13 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__13();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__13);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__14 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__14();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__14);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__15 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__15();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__15);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__16 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__16();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__16);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__17 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__17();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__17);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__18 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__18();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__18);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__19 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__19();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_7257____closed__19);
l_Lean_Parser_instReprLeadingIdentBehavior___closed__1 = _init_l_Lean_Parser_instReprLeadingIdentBehavior___closed__1();
lean_mark_persistent(l_Lean_Parser_instReprLeadingIdentBehavior___closed__1);
l_Lean_Parser_instReprLeadingIdentBehavior = _init_l_Lean_Parser_instReprLeadingIdentBehavior();
lean_mark_persistent(l_Lean_Parser_instReprLeadingIdentBehavior);
l_Lean_Parser_instInhabitedParserCategory___closed__1 = _init_l_Lean_Parser_instInhabitedParserCategory___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserCategory___closed__1);
l_Lean_Parser_instInhabitedParserCategory = _init_l_Lean_Parser_instInhabitedParserCategory();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserCategory);
l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7595____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7595____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7595____closed__1);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7595_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_categoryParserFnRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_categoryParserFnRef);
lean_dec_ref(res);
l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7614____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7614____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7614____closed__1);
l_Lean_Parser_categoryParserFnExtension___closed__1 = _init_l_Lean_Parser_categoryParserFnExtension___closed__1();
lean_mark_persistent(l_Lean_Parser_categoryParserFnExtension___closed__1);
l_Lean_Parser_categoryParserFnExtension___closed__2 = _init_l_Lean_Parser_categoryParserFnExtension___closed__2();
lean_mark_persistent(l_Lean_Parser_categoryParserFnExtension___closed__2);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_7614_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_categoryParserFnExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_categoryParserFnExtension);
lean_dec_ref(res);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___lambda__1___closed__1 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___lambda__1___closed__1);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__1 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__1();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__1);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__2 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__2();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__2);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__3 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__3();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__3);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__4 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__4();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__4);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__5 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__5();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Parser_categoryParserFn___spec__1___closed__5);
l_Lean_Parser_termParser___closed__1 = _init_l_Lean_Parser_termParser___closed__1();
lean_mark_persistent(l_Lean_Parser_termParser___closed__1);
l_Lean_Parser_termParser___closed__2 = _init_l_Lean_Parser_termParser___closed__2();
lean_mark_persistent(l_Lean_Parser_termParser___closed__2);
l_Lean_Parser_checkNoImmediateColon___elambda__1___closed__1 = _init_l_Lean_Parser_checkNoImmediateColon___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_checkNoImmediateColon___elambda__1___closed__1);
l_Lean_Parser_checkNoImmediateColon___closed__1 = _init_l_Lean_Parser_checkNoImmediateColon___closed__1();
lean_mark_persistent(l_Lean_Parser_checkNoImmediateColon___closed__1);
l_Lean_Parser_checkNoImmediateColon___closed__2 = _init_l_Lean_Parser_checkNoImmediateColon___closed__2();
lean_mark_persistent(l_Lean_Parser_checkNoImmediateColon___closed__2);
l_Lean_Parser_checkNoImmediateColon = _init_l_Lean_Parser_checkNoImmediateColon();
lean_mark_persistent(l_Lean_Parser_checkNoImmediateColon);
l_Lean_Parser_pushNone___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_pushNone___elambda__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_pushNone___elambda__1___rarg___closed__1);
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
l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__8 = _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__8();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__8);
l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__9 = _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__9();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__9);
l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__10 = _init_l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__10();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___elambda__1___closed__10);
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
l_Lean_Parser_tokenWithAntiquotFn___lambda__1___closed__1 = _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_tokenWithAntiquotFn___lambda__1___closed__1);
l_Lean_Parser_tokenWithAntiquotFn___lambda__1___closed__2 = _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_tokenWithAntiquotFn___lambda__1___closed__2);
l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__1 = _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__1);
l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__2 = _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__2);
l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__3 = _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__3);
l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__4 = _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__4);
l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__5 = _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__5);
l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__6 = _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__6);
l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__7 = _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__7);
l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__8 = _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__8);
l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__9 = _init_l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Parser_tokenWithAntiquotFn___lambda__2___closed__9);
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
l_Lean_Parser_mkAntiquot___closed__19 = _init_l_Lean_Parser_mkAntiquot___closed__19();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__19);
l_Lean_Parser_mkAntiquot___closed__20 = _init_l_Lean_Parser_mkAntiquot___closed__20();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__20);
l_Lean_Parser_mkAntiquot___closed__21 = _init_l_Lean_Parser_mkAntiquot___closed__21();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__21);
l_Lean_Parser_mkAntiquot___closed__22 = _init_l_Lean_Parser_mkAntiquot___closed__22();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__22);
l_Lean_Parser_mkAntiquot___closed__23 = _init_l_Lean_Parser_mkAntiquot___closed__23();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__23);
l_Lean_Parser_mkAntiquot___closed__24 = _init_l_Lean_Parser_mkAntiquot___closed__24();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__24);
l_Lean_Parser_mkAntiquot___closed__25 = _init_l_Lean_Parser_mkAntiquot___closed__25();
lean_mark_persistent(l_Lean_Parser_mkAntiquot___closed__25);
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
l_Lean_Parser_mkAntiquotSplice___closed__8 = _init_l_Lean_Parser_mkAntiquotSplice___closed__8();
lean_mark_persistent(l_Lean_Parser_mkAntiquotSplice___closed__8);
l_Lean_Parser_mkAntiquotSplice___closed__9 = _init_l_Lean_Parser_mkAntiquotSplice___closed__9();
lean_mark_persistent(l_Lean_Parser_mkAntiquotSplice___closed__9);
l_Lean_Parser_mkAntiquotSplice___closed__10 = _init_l_Lean_Parser_mkAntiquotSplice___closed__10();
lean_mark_persistent(l_Lean_Parser_mkAntiquotSplice___closed__10);
l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__1 = _init_l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__1);
l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__2 = _init_l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__2);
l_Lean_Parser_sepByElemParser___closed__1 = _init_l_Lean_Parser_sepByElemParser___closed__1();
lean_mark_persistent(l_Lean_Parser_sepByElemParser___closed__1);
l_Lean_Parser_sepByElemParser___closed__2 = _init_l_Lean_Parser_sepByElemParser___closed__2();
lean_mark_persistent(l_Lean_Parser_sepByElemParser___closed__2);
l_Lean_Parser_sepByElemParser___closed__3 = _init_l_Lean_Parser_sepByElemParser___closed__3();
lean_mark_persistent(l_Lean_Parser_sepByElemParser___closed__3);
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
l_Lean_Parser_evalParserConstUnsafe___closed__5 = _init_l_Lean_Parser_evalParserConstUnsafe___closed__5();
lean_mark_persistent(l_Lean_Parser_evalParserConstUnsafe___closed__5);
l_Lean_Parser_evalParserConstUnsafe___closed__6 = _init_l_Lean_Parser_evalParserConstUnsafe___closed__6();
lean_mark_persistent(l_Lean_Parser_evalParserConstUnsafe___closed__6);
l_Lean_Parser_evalParserConstUnsafe___closed__7 = _init_l_Lean_Parser_evalParserConstUnsafe___closed__7();
lean_mark_persistent(l_Lean_Parser_evalParserConstUnsafe___closed__7);
l_Lean_Parser_evalParserConstUnsafe___closed__8 = _init_l_Lean_Parser_evalParserConstUnsafe___closed__8();
lean_mark_persistent(l_Lean_Parser_evalParserConstUnsafe___closed__8);
l_Lean_Parser_evalParserConstUnsafe___closed__9 = _init_l_Lean_Parser_evalParserConstUnsafe___closed__9();
lean_mark_persistent(l_Lean_Parser_evalParserConstUnsafe___closed__9);
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
l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__2 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__2();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__2);
l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__3 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__3();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__3);
l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__4 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__4();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__4);
l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__5 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__5();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__5);
l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__6 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__6();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755____closed__6);
l_Lean_Parser_internal_parseQuotWithCurrentStage___closed__1 = _init_l_Lean_Parser_internal_parseQuotWithCurrentStage___closed__1();
lean_mark_persistent(l_Lean_Parser_internal_parseQuotWithCurrentStage___closed__1);
res = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_8755_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_internal_parseQuotWithCurrentStage = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_internal_parseQuotWithCurrentStage);
lean_dec_ref(res);
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
l_Lean_Parser_fieldIdx___closed__8 = _init_l_Lean_Parser_fieldIdx___closed__8();
lean_mark_persistent(l_Lean_Parser_fieldIdx___closed__8);
l_Lean_Parser_fieldIdx___closed__9 = _init_l_Lean_Parser_fieldIdx___closed__9();
lean_mark_persistent(l_Lean_Parser_fieldIdx___closed__9);
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
