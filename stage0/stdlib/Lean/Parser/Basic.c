// Lean compiler output
// Module: Lean.Parser.Basic
// Imports: Lean.Parser.Types
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
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrec(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_categoryParserFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserCategory;
static lean_object* l_Lean_Parser_nameLitNoAntiquot___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEq(lean_object*);
static lean_object* l_Lean_Parser_sepByElemParser___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_mkAntiquot_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___elambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__17;
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharFn(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__4(lean_object*);
static lean_object* l_Lean_Parser_nameLitFn___closed__3;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone;
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_decQuotDepth(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8964____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nameLitNoAntiquot;
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEqFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_error(lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo___elambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeStringParser;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__4;
static lean_object* l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__2___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos___elambda__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutInfo___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_skip___elambda__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_toCtorIdx___boxed(lean_object*);
static lean_object* l_Lean_Parser_invalidLongestMatchParser___closed__1;
static lean_object* l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__5;
static lean_object* l_Lean_Parser_strLitFnAux___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_identEqFn___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqRecoveryContext;
static lean_object* l_Lean_Parser_instReprRecoveryContext___closed__1;
static lean_object* l_Lean_Parser_mkAntiquot___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__14;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkColGe_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_stringGapFn___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAtomicInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot___boxed(lean_object*);
static lean_object* l_Lean_Parser_charLitFnAux___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_toCtorIdx(uint8_t);
static lean_object* l_Lean_Parser_dbgTraceStateFn___closed__3;
static lean_object* l_Lean_Parser_decimalNumberFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_decimalNumberFn_parseOptExp___lambda__1(uint32_t, uint32_t, uint32_t);
static lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrecFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_andthen___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strAux_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo___elambda__2(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_decQuotDepth___closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_recover_docString__1___closed__3;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__18;
lean_object* l_Lean_Parser_Error_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__7;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__5;
static lean_object* l_Lean_Parser_TokenMap_instForInProdNameList___closed__2;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_satisfyFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion(lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2;
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_224____spec__1(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1;
uint8_t l_Lean_RBNode_isRed___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_binNumberFn___lambda__1(uint32_t);
static lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___elambda__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instBEqRecoveryContext___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_quotedStringFn(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_recover(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__12;
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1___boxed__const__2;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__13;
static lean_object* l_Lean_Parser_mkAntiquot___closed__11;
static lean_object* l_Lean_Parser_optionalFn___closed__1;
lean_object* l_Lean_Parser_SyntaxStack_size(lean_object*);
static lean_object* l_Lean_Parser_checkNoImmediateColon___elambda__1___closed__1;
static lean_object* l_Lean_Parser_charLitNoAntiquot___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_fieldIdx___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqOrElseOnAntiquotBehavior____x40_Lean_Parser_Basic___hyg_665____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo___elambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTop___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_identFn___closed__2;
static lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_dbgTraceStateFn___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_unicodeSymbolFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at_Lean_Syntax_forArgsM___spec__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___elambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdxFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo___elambda__2(lean_object*);
static lean_object* l_Lean_Parser_skip___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__2___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext;
static lean_object* l_Lean_Parser_hexNumberFn___closed__1;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__20;
static lean_object* l___regBuiltin_Lean_Parser_atomic_docString__1___closed__2;
static lean_object* l_Lean_Parser_finishCommentBlock_eoi___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_octalNumberFn___lambda__1(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9445_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharDefault___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquotSplice___closed__4;
static lean_object* l_Lean_Parser_strLitFnAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__11;
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_TokenMap_instForInProdNameList___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameList(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_optionalFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__2;
static lean_object* l_Lean_Parser_nonReservedSymbolInfo___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_indexed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPosFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_unicodeSymbolInfo___closed__1;
LEAN_EXPORT uint8_t l_Lean_Parser_isIdCont(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext___boxed(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__3;
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__2(lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2;
lean_object* l_Lean_Parser_withCacheFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__10;
LEAN_EXPORT uint8_t l_Lean_Parser_symbolFnAux___lambda__1(lean_object*, lean_object*);
uint8_t l___private_Lean_Parser_Types_0__Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_440_(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_dbgTraceStateFn___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint32_t l_Lean_idBeginEscape;
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9471____closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___elambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isIdCont___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__7;
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_epsilonInfo___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdx;
static lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at_Lean_Syntax_forArgsM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Fn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_skip___elambda__1(lean_object*);
static lean_object* l_Lean_Parser_mkTokenAndFixPos___closed__1;
static lean_object* l_Lean_Parser_mkAntiquot___closed__15;
static lean_object* l_Lean_Parser_strLitNoAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___elambda__1___rarg(lean_object*);
static lean_object* l_Lean_Parser_instBEqLeadingIdentBehavior___closed__1;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__17;
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__10;
static lean_object* l_Lean_Parser_checkNoImmediateColon___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_atomic_docString__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnExtension;
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh(uint32_t, uint8_t);
static lean_object* l_Lean_Parser_nonReservedSymbolInfo___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo___elambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_termParser___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrecFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Parser_instReprLeadingIdentBehavior___closed__1;
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_Lean_Parser_longestMatchFn___closed__1;
static lean_object* l_Lean_Parser_whitespace___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepLatest___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_Parser_fieldIdx___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_binNumberFn___closed__1;
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__3;
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol___boxed(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1(lean_object*);
static lean_object* l_Lean_Parser_hexNumberFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkEmptySubstringAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock_eoi(uint8_t, lean_object*);
static lean_object* l_Lean_Parser_rawIdentNoAntiquot___closed__1;
static lean_object* l_Lean_Parser_eoi___closed__1;
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__3;
static lean_object* l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__2;
static lean_object* l_Lean_Parser_dbgTraceStateFn___closed__2;
static lean_object* l_Lean_Parser_fieldIdxFn___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos(lean_object*, uint8_t);
static lean_object* l_Lean_Parser_instBEqOrElseOnAntiquotBehavior___closed__1;
static lean_object* l_Lean_Parser_mkAntiquot___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at_Lean_Parser_checkTailLinebreak___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__1___closed__1;
lean_object* l_Lean_Parser_SyntaxStack_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__7;
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_lookaheadFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_eoiFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Parser_identFnAux_parse___closed__3;
static lean_object* l___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6(lean_object*);
static lean_object* l_Lean_Parser_hexDigitFn___closed__1;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__19;
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailWs___boxed(lean_object*);
static lean_object* l_Lean_Parser_antiquotExpr___closed__2;
static lean_object* l_Lean_Parser_strLitFn___closed__1;
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__10;
static lean_object* l___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_orelse___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo;
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot(lean_object*);
static lean_object* l_Lean_Parser_dbgTraceStateFn___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_eoi;
static lean_object* l_Lean_Parser_quotedCharCoreFn___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition(lean_object*);
static lean_object* l_Lean_Parser_incQuotDepth___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoNoAntiquot;
static lean_object* l_Lean_Parser_errorAtSavedPos___closed__2;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_stringGapFn___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_atomic_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_charLitFn___closed__1;
static lean_object* l_Lean_Parser_symbolInfo___closed__1;
static lean_object* l_Lean_Parser_categoryParserFn___closed__2;
LEAN_EXPORT uint8_t l_Lean_Parser_instInhabitedLeadingIdentBehavior;
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptDot(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_normalState___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFnAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrec___elambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_suppressInsideQuot___closed__1;
lean_object* l_Lean_Parser_ParserState_next(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe___elambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object*, uint8_t);
static lean_object* l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_withoutForbidden___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_identEqFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_charLitNoAntiquot;
lean_object* l_lexOrd___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyNoAntiquot___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_skip___elambda__1___rarg___boxed(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg___boxed(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2;
static lean_object* l_Lean_Parser_identNoAntiquot___closed__2;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_size___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptDot___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_adaptCacheableContext(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_fieldIdxFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_fieldIdx___closed__3;
static lean_object* l___regBuiltin_Lean_Parser_lookahead_docString__1___closed__3;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__16;
static lean_object* l_Lean_Parser_decimalNumberFn_parseScientific___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_recover_docString__1(lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_mergeOrElseErrors(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Parser_scientificLitNoAntiquot___closed__1;
static lean_object* l_Lean_Parser_mkAntiquot___closed__12;
static lean_object* l_Lean_Parser_manyAux___lambda__3___closed__1;
static lean_object* l_Lean_Parser_identEqFn___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identEq___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_identNoAntiquot___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9445____lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquotSplice___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp___boxed__const__1;
static lean_object* l_Lean_Parser_checkPrecFn___closed__1;
static lean_object* l_Lean_Parser_fieldIdx___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAtomicInfo___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrec___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_normalState(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentNoAntiquot;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTop___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkLineEq_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrec___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at_Lean_Syntax_foldArgs___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquotSplice___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1;
static lean_object* l_Lean_Parser_sepByElemParser___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_node___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_longestMatchStep___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_identEqFn___closed__2;
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_takeWhileFn___lambda__1(lean_object*, uint32_t);
static lean_object* l_Lean_Parser_dbgTraceStateFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbol(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optionaInfo(lean_object*);
static lean_object* l_Lean_Parser_strLitNoAntiquot___closed__3;
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqOrElseOnAntiquotBehavior____x40_Lean_Parser_Basic___hyg_665_(uint8_t, uint8_t);
static lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__3;
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailWs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9445____lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM(lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_orelse_docString__1___closed__1;
static lean_object* l___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__3;
static lean_object* l_Lean_Parser_termParser___closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at_Lean_Syntax_forArgsM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrec___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_lookahead_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon;
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lambda__1(lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__5;
lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9445____closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_errorAtSavedPos___closed__1;
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo___elambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1;
static lean_object* l___regBuiltin_Lean_Parser_recover_docString__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_atomic___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_optionalNoAntiquot___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__17;
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at_Lean_Parser_checkTailLinebreak___spec__1(uint32_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_scientificLitNoAntiquot___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_numLitFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo___elambda__1___boxed(lean_object*);
static lean_object* l_Lean_Parser_strLitFnAux___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isIdEndEscape___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_atomic_docString__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_nameLitFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak(lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_recover_docString__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Parser_fieldIdx___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_numLitNoAntiquot___closed__3;
LEAN_EXPORT uint8_t l_Lean_Parser_isRawStrLitStart(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___lambda__1(lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__14;
static lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOf___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTopFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lambda__1___boxed(lean_object*);
lean_object* l_Lean_isIdRest___boxed(lean_object*);
static lean_object* l_Lean_Parser_skip___closed__2;
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo___elambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrecFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_eoi___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withForbidden_docString__1(lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___elambda__1___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474_(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParserCategory___closed__3;
static lean_object* l_Lean_Parser_decimalNumberFn_parseScientific___closed__2;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1___boxed__const__1;
lean_object* l_instOrdNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_optionaInfo___elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseScientific(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_orelse_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1NoAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_node(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_chFn(uint32_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs(lean_object*);
lean_object* l_Pi_instInhabited___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isRawStrLitStart___boxed(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg___boxed(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_numLitNoAntiquot;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__14;
static lean_object* l_Lean_Parser_numLitNoAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_closingState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(uint32_t);
static lean_object* l_Lean_Parser_anyOfFn___closed__1;
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTopFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_hygieneInfoNoAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkWsBefore_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_charLitNoAntiquot___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_optionaInfo___elambda__2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_mergeOrElseErrors___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqLeadingIdentBehavior;
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp___boxed__const__2;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhile1Fn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_peekTokenAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe(lean_object*);
static lean_object* l_Lean_Parser_instCoeStringParser___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeAux___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_whitespace___closed__3;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo___elambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_whitespace___lambda__1(uint32_t, uint32_t);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__4;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrec___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_categoryParserFn___lambda__1___closed__1;
lean_object* l_Lean_Data_Trie_matchPrefix___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_atomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotNestedExpr;
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_unicodeSymbolFnAux___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_notFollowedBy_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info___elambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2(lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqRecoveryContext____x40_Lean_Parser_Basic___hyg_1255____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_binNumberFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9471____lambda__1(lean_object*);
static lean_object* l_Lean_Parser_many1Unbox___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___lambda__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_identNoAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__2(lean_object*);
static lean_object* l_Lean_Parser_charLitFnAux___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nameLitFn(lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1;
static lean_object* l___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot___elambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info___elambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__6;
static lean_object* l_Lean_Parser_dbgTraceStateFn___closed__5;
uint8_t l_Lean_isLetterLike(uint32_t);
static lean_object* l___regBuiltin_Lean_Parser_orelse_docString__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___elambda__1___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decEqRecoveryContext____x40_Lean_Parser_Basic___hyg_1329____boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__15;
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_checkNoImmediateColon___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkTokenAndFixPos___closed__2;
static lean_object* l_Lean_Parser_hygieneInfoNoAntiquot___closed__3;
static lean_object* l___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquotSplice___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_scientificLitFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__8;
LEAN_EXPORT uint8_t l_Lean_Parser_decimalNumberFn___lambda__1(uint32_t);
lean_object* l_Subarray_get___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9471_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_identFnAux_parse___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited(lean_object*);
lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLitFn(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_categoryParserFn___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_withPosition_docString__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_hexNumberFn___lambda__1(uint32_t);
static lean_object* l___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__3;
static lean_object* l_Lean_Parser_decimalNumberFn___closed__2;
static lean_object* l_Lean_Parser_numberFnAux___closed__1;
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_decimalNumberFn___closed__3;
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_charLitNoAntiquot___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3;
static lean_object* l_Lean_Parser_mkAntiquot___closed__9;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_replaceLongest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_sepByElemParser___closed__2;
static lean_object* l_Lean_Parser_pushNone___elambda__1___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot(lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__6(lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_identEqFn___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot___elambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__15;
lean_object* l_id___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_error___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoopStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_strLitNoAntiquot___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_incQuotDepth(lean_object*);
uint32_t l_Lean_Parser_getNext(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_skip;
LEAN_EXPORT lean_object* l_Lean_Parser_andthenInfo___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_recoverFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLitNoAntiquot;
lean_object* l_Lean_RBMap_instForInProd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strLitNoAntiquot;
LEAN_EXPORT lean_object* l_Lean_Parser_runLongestMatchParser___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2;
static lean_object* l_Lean_Parser_takeDigitsFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_octalNumberFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at_Lean_Syntax_foldArgs___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1;
static lean_object* l_Lean_Parser_mkAntiquot___closed__13;
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrec(lean_object*);
static lean_object* l_Lean_Parser_pushNone___elambda__1___rarg___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withoutPosition_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__6;
static lean_object* l_Lean_Parser_nameLitNoAntiquot___closed__3;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock_eoi___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_strLitFnAux___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___elambda__2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_UInt32_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withPosition_docString__1(lean_object*);
static lean_object* l_Lean_Parser_orelseFnCore___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEq___elambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_chFn___closed__1;
uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_next_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOf(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq(lean_object*);
static lean_object* l_Lean_Parser_whitespace___closed__4;
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_decEqRecoveryContext____x40_Lean_Parser_Basic___hyg_1329_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_errorUnterminated(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqRecoveryContext____x40_Lean_Parser_Basic___hyg_1255_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo___elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotExpr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_whitespace___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_antiquotExpr;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedPrattParsingTables;
LEAN_EXPORT lean_object* l_Lean_Parser_atomicFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_maxPrec;
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2;
static lean_object* l_Lean_Parser_rawIdentNoAntiquot___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPosFn(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo___elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identFn(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_charLitFnAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_identNoAntiquot;
LEAN_EXPORT lean_object* l_Lean_Parser_error___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__6;
static lean_object* l_Lean_Parser_pushNone___closed__1;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Parser_withCacheFn___spec__7(lean_object*);
lean_object* l_Lean_Parser_FirstTokens_seq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection(lean_object*);
static lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp___closed__2;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__9;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__16;
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__12;
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_epsilonInfo___closed__1;
static lean_object* l_Lean_Parser_octalNumberFn___closed__2;
static lean_object* l_Lean_Parser_quotedCharCoreFn___closed__4;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1(lean_object*);
static lean_object* l_Lean_Parser_quotedCharCoreFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strAux_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___elambda__1___boxed(lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___elambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_identEqFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_identFnAux_parse___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_initState(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead(lean_object*);
static lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9471____lambda__1___closed__1;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__10;
static lean_object* l___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1;
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_nonReservedSymbolInfo___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lambda__1___boxed(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8964_(uint8_t, uint8_t);
static lean_object* l_Lean_Parser_antiquotExpr___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_recover_x27_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_invalidLongestMatchParser(lean_object*);
static lean_object* l_Lean_Parser_orelseFnCore___lambda__1___closed__1;
static lean_object* l_Lean_Parser_quotedCharCoreFn___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mergeErrors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailLinebreak(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1NoAntiquot___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__18;
static lean_object* l_Lean_Parser_scientificLitNoAntiquot___closed__2;
static lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__5;
static lean_object* l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEqFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore___elambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__3;
lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkColEq_docString__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_orelse_docString__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at_Lean_Syntax_foldArgs___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox(lean_object*);
static lean_object* l_Lean_Parser_numLitNoAntiquot___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGeFn(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailLinebreak___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailNoWs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___elambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_errorFn___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_nameLitFn___closed__1;
static lean_object* l_Lean_Parser_mkAntiquotSplice___closed__3;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_peekToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__11;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___lambda__1(lean_object*);
static lean_object* l_Lean_Parser_antiquotExpr___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withAntiquot_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_closingState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquotSplice___closed__2;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_hygieneInfoFn___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrec(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailNoWs(lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1;
static lean_object* l_Lean_Parser_fieldIdxFn___closed__1;
static lean_object* l_Lean_Parser_longestMatchStep___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedPrattParsingTables___closed__1;
static lean_object* l___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_identEq(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_notFollowedByFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGtFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_manyNoAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_strAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParserCategory___closed__1;
static lean_object* l___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_anyOfFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___elambda__1(uint32_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_instInhabitedParserFn___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqOrElseOnAntiquotBehavior;
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrec___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__3;
lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParser(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnRef;
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_skip___elambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq___elambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__16;
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__19;
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition(lean_object*);
static lean_object* l_Lean_Parser_nonReservedSymbolInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_instInhabitedParserCategory___closed__2;
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquots(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instAndThenParser(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt(lean_object*);
static lean_object* l_Lean_Parser_identFn___closed__1;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__1;
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__13;
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2;
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2;
static lean_object* l_Lean_Parser_hygieneInfoFn___lambda__1___closed__2;
static lean_object* l___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot(lean_object*);
static lean_object* l_Lean_Parser_dbgTraceStateFn___closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkColGt_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepNewError___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__9;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withoutForbidden_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_mkAntiquot___closed__10;
static lean_object* l_Lean_Parser_quotedCharFn___closed__1;
static lean_object* l_Lean_Parser_antiquotNestedExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_optionalFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_pushNone___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_hygieneInfoNoAntiquot___closed__2;
static lean_object* l_Lean_Parser_epsilonInfo___closed__3;
static lean_object* l_Lean_Parser_nameLitNoAntiquot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_epsilonInfo___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_termParser(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceState___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_FirstTokens_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_withoutPosition___closed__1;
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
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_dbgTraceStateFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n  pos: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_dbgTraceStateFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n  err: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_dbgTraceStateFn___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_dbgTraceStateFn___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("none", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_dbgTraceStateFn___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n  out: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_dbgTraceStateFn___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(some ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_dbgTraceStateFn___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_dbgTraceStateFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = l_Lean_Parser_SyntaxStack_size(x_5);
lean_dec(x_5);
x_7 = lean_apply_2(x_2, x_3, x_4);
x_8 = l_Lean_Parser_dbgTraceStateFn___closed__1;
x_9 = lean_string_append(x_8, x_1);
x_10 = l_Lean_Parser_dbgTraceStateFn___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
x_13 = l___private_Init_Data_Repr_0__Nat_reprFast(x_12);
x_14 = lean_string_append(x_11, x_13);
lean_dec(x_13);
x_15 = l_Lean_Parser_dbgTraceStateFn___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_ctor_get(x_7, 4);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
x_19 = l_Lean_Parser_SyntaxStack_size(x_18);
x_20 = l_Lean_Parser_SyntaxStack_extract(x_18, x_6, x_19);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_18);
x_21 = lean_array_to_list(x_20);
x_22 = l_List_toString___at_Lean_Parser_withCacheFn___spec__7(x_21);
x_23 = l_Lean_Parser_dbgTraceStateFn___closed__4;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_alloc_closure((void*)(l_Lean_Parser_dbgTraceStateFn___lambda__1___boxed), 2, 1);
lean_closure_set(x_25, 0, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = l_Lean_Parser_dbgTraceStateFn___closed__5;
x_27 = lean_string_append(x_16, x_26);
x_28 = l_Lean_Parser_dbgTraceStateFn___closed__6;
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
x_36 = l_Lean_Parser_dbgTraceStateFn___closed__7;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Lean_Parser_dbgTraceStateFn___closed__8;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_string_append(x_16, x_39);
lean_dec(x_39);
x_41 = l_Lean_Parser_dbgTraceStateFn___closed__6;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_string_append(x_42, x_24);
lean_dec(x_24);
x_44 = lean_string_append(x_43, x_8);
x_45 = lean_dbg_trace(x_44, x_25);
return x_45;
}
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
x_6 = l_Lean_Parser_SyntaxStack_back(x_5);
lean_dec(x_5);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = 1;
x_11 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_2, x_9, x_10);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTop___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_checkStackTopFn(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_checkStackTop___elambda__1___boxed), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = l_Lean_Parser_epsilonInfo;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkStackTop___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_checkStackTop___elambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
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
x_8 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Parser_andthen___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_andthenFn(x_1, x_2, x_3, x_4);
return x_5;
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
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_andthen___elambda__1), 4, 2);
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_2, x_3);
x_5 = l_Lean_Parser_andthen(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Parser_ParserState_stackSize(x_4);
x_6 = lean_apply_2(x_2, x_3, x_4);
x_7 = l_Lean_Parser_ParserState_mkNode(x_6, x_1, x_5);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Parser_ParserState_stackSize(x_4);
x_6 = lean_apply_2(x_2, x_3, x_4);
x_7 = l_Lean_Parser_ParserState_mkTrailingNode(x_6, x_1, x_5);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeInfo___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_3);
x_6 = lean_box(0);
x_7 = l_Lean_PersistentHashMap_insert___at_Lean_Parser_SyntaxNodeKindSet_insert___spec__1(x_5, x_1, x_6);
return x_7;
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
LEAN_EXPORT lean_object* l_Lean_Parser_node___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_nodeFn(x_1, x_2, x_3, x_4);
return x_5;
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
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_node___elambda__1), 4, 2);
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
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 1;
x_6 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_1, x_4, x_5);
return x_6;
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
LEAN_EXPORT lean_object* l_Lean_Parser_error___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_errorFn(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_error(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_error___elambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_epsilonInfo;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_error___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_error___elambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPosFn(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
else
{
if (x_2 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_4, x_1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_string_utf8_next(x_11, x_9);
lean_dec(x_9);
lean_dec(x_11);
x_13 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_4, x_1, x_12);
return x_13;
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
static lean_object* _init_l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("errorAtSavedPos", 15, 15);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Generate an error at the position saved with the `withPosition` combinator.\nIf `delta == true`, then it reports at saved position+1.\nThis useful to make sure a parser consumed at least one character.  ", 201, 201);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__4;
x_3 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__5;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos___elambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_errorAtSavedPosFn(x_1, x_2, x_3, x_4);
return x_5;
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
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_errorAtSavedPos___elambda__1___boxed), 4, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = l_Lean_Parser_errorAtSavedPos___closed__2;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_errorAtSavedPos___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Parser_errorAtSavedPos___elambda__1(x_1, x_5, x_3, x_4);
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
x_1 = lean_mk_string_unchecked("unexpected token at this precedence level; consider parenthesizing the term", 75, 75);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrecFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_nat_dec_le(x_5, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_box(0);
x_8 = l_Lean_Parser_checkPrecFn___closed__1;
x_9 = 1;
x_10 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_8, x_7, x_9);
return x_10;
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
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrec___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkPrecFn(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrec(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkPrec___elambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_epsilonInfo;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkPrec___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkPrec___elambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_box(0);
x_7 = l_Lean_Parser_checkPrecFn___closed__1;
x_8 = 1;
x_9 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_7, x_6, x_8);
return x_9;
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
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrec___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkLhsPrecFn(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrec(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkLhsPrec___elambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_epsilonInfo;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLhsPrec___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkLhsPrec___elambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrecFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 4);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 5);
lean_inc(x_8);
x_9 = lean_box(0);
lean_inc(x_7);
x_10 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_9);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_3, 5);
lean_dec(x_12);
x_13 = lean_ctor_get(x_3, 4);
lean_dec(x_13);
x_14 = lean_ctor_get(x_3, 3);
lean_dec(x_14);
x_15 = lean_ctor_get(x_3, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_3, 0);
lean_dec(x_17);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
else
{
lean_object* x_18; 
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set(x_18, 2, x_5);
lean_ctor_set(x_18, 3, x_6);
lean_ctor_set(x_18, 4, x_7);
lean_ctor_set(x_18, 5, x_8);
return x_18;
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
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrec___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_setLhsPrecFn(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrec(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_setLhsPrec___elambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_epsilonInfo;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setLhsPrec___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_setLhsPrec___elambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_nat_to_int(x_4);
x_6 = lean_int_add(x_5, x_1);
lean_dec(x_5);
x_7 = l_Int_toNat(x_6);
lean_dec(x_6);
lean_ctor_set(x_2, 1, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_13 = lean_nat_to_int(x_9);
x_14 = lean_int_add(x_13, x_1);
lean_dec(x_13);
x_15 = l_Int_toNat(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_10);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Parser_adaptCacheableContext(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
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
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_incQuotDepth___closed__1;
x_3 = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth(x_2, x_1);
return x_3;
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
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_decQuotDepth___closed__1;
x_3 = l___private_Lean_Parser_Basic_0__Lean_Parser_addQuotDepth(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 3);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
x_13 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_13);
return x_1;
}
else
{
uint8_t x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = 1;
x_15 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_4);
lean_ctor_set(x_15, 3, x_5);
lean_ctor_set_uint8(x_15, sizeof(void*)*4, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l_Lean_Parser_suppressInsideQuot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_suppressInsideQuot___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_suppressInsideQuot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_suppressInsideQuot___closed__1;
x_3 = l_Lean_Parser_adaptCacheableContext(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingNode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_4 = l_Lean_Parser_checkPrec(x_2);
x_5 = l_Lean_Parser_node(x_1, x_3);
x_6 = l_Lean_Parser_setLhsPrec(x_2);
x_7 = l_Lean_Parser_andthen(x_5, x_6);
x_8 = l_Lean_Parser_andthen(x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingNodeAux___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_trailingNodeFn(x_1, x_2, x_3, x_4);
return x_5;
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
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_trailingNodeAux___elambda__1), 4, 2);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_5 = l_Lean_Parser_checkPrec(x_2);
x_6 = l_Lean_Parser_checkLhsPrec(x_3);
x_7 = l_Lean_Parser_trailingNodeAux(x_1, x_4);
x_8 = l_Lean_Parser_setLhsPrec(x_2);
x_9 = l_Lean_Parser_andthen(x_7, x_8);
x_10 = l_Lean_Parser_andthen(x_6, x_9);
x_11 = l_Lean_Parser_andthen(x_5, x_10);
return x_11;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 5);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_nat_dec_eq(x_8, x_3);
if (x_13 == 0)
{
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_1, 5);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 4);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 3);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_1, 0);
lean_dec(x_20);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_21; 
x_21 = l_Lean_Parser_Error_merge(x_2, x_12);
lean_ctor_set(x_5, 0, x_21);
return x_1;
}
}
else
{
lean_dec(x_1);
if (x_4 == 0)
{
lean_object* x_22; 
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_7);
lean_ctor_set(x_22, 2, x_8);
lean_ctor_set(x_22, 3, x_9);
lean_ctor_set(x_22, 4, x_5);
lean_ctor_set(x_22, 5, x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Parser_Error_merge(x_2, x_12);
lean_ctor_set(x_5, 0, x_23);
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_7);
lean_ctor_set(x_24, 2, x_8);
lean_ctor_set(x_24, 3, x_9);
lean_ctor_set(x_24, 4, x_5);
lean_ctor_set(x_24, 5, x_10);
return x_24;
}
}
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_5, 0);
lean_inc(x_25);
lean_dec(x_5);
x_26 = lean_nat_dec_eq(x_8, x_3);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_27; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 x_27 = x_1;
} else {
 lean_dec_ref(x_1);
 x_27 = lean_box(0);
}
if (x_4 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 6, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_7);
lean_ctor_set(x_29, 2, x_8);
lean_ctor_set(x_29, 3, x_9);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set(x_29, 5, x_10);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lean_Parser_Error_merge(x_2, x_25);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
if (lean_is_scalar(x_27)) {
 x_32 = lean_alloc_ctor(0, 6, 0);
} else {
 x_32 = x_27;
}
lean_ctor_set(x_32, 0, x_6);
lean_ctor_set(x_32, 1, x_7);
lean_ctor_set(x_32, 2, x_8);
lean_ctor_set(x_32, 3, x_9);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_10);
return x_32;
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
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqOrElseOnAntiquotBehavior____x40_Lean_Parser_Basic___hyg_665_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx(x_1);
x_4 = l_Lean_Parser_OrElseOnAntiquotBehavior_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqOrElseOnAntiquotBehavior____x40_Lean_Parser_Basic___hyg_665____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Parser_Basic_0__Lean_Parser_beqOrElseOnAntiquotBehavior____x40_Lean_Parser_Basic___hyg_665_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_instBEqOrElseOnAntiquotBehavior___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_beqOrElseOnAntiquotBehavior____x40_Lean_Parser_Basic___hyg_665____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instBEqOrElseOnAntiquotBehavior() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_orelseFnCore___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("choice", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_orelseFnCore___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_orelseFnCore___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 5);
lean_inc(x_10);
x_11 = l_Lean_Parser_SyntaxStack_back(x_5);
lean_dec(x_5);
lean_inc(x_3);
x_12 = l_Lean_Parser_ParserState_popSyntax(x_3);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_3, 5);
lean_dec(x_14);
x_15 = lean_ctor_get(x_3, 4);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 3);
lean_dec(x_16);
x_17 = lean_ctor_get(x_3, 2);
lean_dec(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_3, 0);
lean_dec(x_19);
x_20 = l_Lean_Parser_orelseFnCore___lambda__1___closed__2;
lean_inc(x_1);
x_21 = l_Lean_Syntax_isOfKind(x_1, x_20);
lean_inc(x_11);
x_22 = l_Lean_Syntax_isOfKind(x_11, x_20);
if (x_21 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_Parser_ParserState_pushSyntax(x_12, x_1);
if (x_22 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_3);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_24 = l_Lean_Parser_ParserState_pushSyntax(x_23, x_11);
x_25 = l_Lean_Parser_ParserState_mkNode(x_24, x_20, x_2);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = l_Array_append___rarg(x_29, x_27);
lean_dec(x_27);
lean_ctor_set(x_26, 0, x_30);
lean_ctor_set(x_3, 0, x_26);
x_31 = l_Lean_Parser_ParserState_mkNode(x_3, x_20, x_2);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = l_Array_append___rarg(x_32, x_27);
lean_dec(x_27);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_3, 0, x_35);
x_36 = l_Lean_Parser_ParserState_mkNode(x_3, x_20, x_2);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_12, 0);
lean_inc(x_37);
lean_dec(x_12);
x_38 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 0);
x_41 = l_Array_append___rarg(x_40, x_38);
lean_dec(x_38);
if (x_22 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_ctor_set(x_37, 0, x_41);
lean_ctor_set(x_3, 0, x_37);
x_42 = l_Lean_Parser_ParserState_pushSyntax(x_3, x_11);
x_43 = l_Lean_Parser_ParserState_mkNode(x_42, x_20, x_2);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_45 = l_Array_append___rarg(x_41, x_44);
lean_dec(x_44);
lean_ctor_set(x_37, 0, x_45);
lean_ctor_set(x_3, 0, x_37);
x_46 = l_Lean_Parser_ParserState_mkNode(x_3, x_20, x_2);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_37, 0);
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_37);
x_49 = l_Array_append___rarg(x_47, x_38);
lean_dec(x_38);
if (x_22 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set(x_3, 0, x_50);
x_51 = l_Lean_Parser_ParserState_pushSyntax(x_3, x_11);
x_52 = l_Lean_Parser_ParserState_mkNode(x_51, x_20, x_2);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_54 = l_Array_append___rarg(x_49, x_53);
lean_dec(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_48);
lean_ctor_set(x_3, 0, x_55);
x_56 = l_Lean_Parser_ParserState_mkNode(x_3, x_20, x_2);
return x_56;
}
}
}
}
else
{
lean_object* x_57; uint8_t x_58; uint8_t x_59; 
lean_dec(x_3);
x_57 = l_Lean_Parser_orelseFnCore___lambda__1___closed__2;
lean_inc(x_1);
x_58 = l_Lean_Syntax_isOfKind(x_1, x_57);
lean_inc(x_11);
x_59 = l_Lean_Syntax_isOfKind(x_11, x_57);
if (x_58 == 0)
{
lean_object* x_60; 
x_60 = l_Lean_Parser_ParserState_pushSyntax(x_12, x_1);
if (x_59 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_61 = l_Lean_Parser_ParserState_pushSyntax(x_60, x_11);
x_62 = l_Lean_Parser_ParserState_mkNode(x_61, x_57, x_2);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec(x_60);
x_64 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_67 = x_63;
} else {
 lean_dec_ref(x_63);
 x_67 = lean_box(0);
}
x_68 = l_Array_append___rarg(x_65, x_64);
lean_dec(x_64);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
x_70 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_6);
lean_ctor_set(x_70, 2, x_7);
lean_ctor_set(x_70, 3, x_8);
lean_ctor_set(x_70, 4, x_9);
lean_ctor_set(x_70, 5, x_10);
x_71 = l_Lean_Parser_ParserState_mkNode(x_70, x_57, x_2);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_12, 0);
lean_inc(x_72);
lean_dec(x_12);
x_73 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
x_77 = l_Array_append___rarg(x_74, x_73);
lean_dec(x_73);
if (x_59 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
x_79 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_6);
lean_ctor_set(x_79, 2, x_7);
lean_ctor_set(x_79, 3, x_8);
lean_ctor_set(x_79, 4, x_9);
lean_ctor_set(x_79, 5, x_10);
x_80 = l_Lean_Parser_ParserState_pushSyntax(x_79, x_11);
x_81 = l_Lean_Parser_ParserState_mkNode(x_80, x_57, x_2);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_83 = l_Array_append___rarg(x_77, x_82);
lean_dec(x_82);
if (lean_is_scalar(x_76)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_76;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_75);
x_85 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_6);
lean_ctor_set(x_85, 2, x_7);
lean_ctor_set(x_85, 3, x_8);
lean_ctor_set(x_85, 4, x_9);
lean_ctor_set(x_85, 5, x_10);
x_86 = l_Lean_Parser_ParserState_mkNode(x_85, x_57, x_2);
return x_86;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
x_8 = lean_nat_dec_lt(x_7, x_3);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; 
x_9 = 2;
x_10 = l___private_Lean_Parser_Basic_0__Lean_Parser_beqOrElseOnAntiquotBehavior____x40_Lean_Parser_Basic___hyg_665_(x_4, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Parser_ParserState_restore(x_5, x_2, x_3);
x_12 = l_Lean_Parser_ParserState_pushSyntax(x_11, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l_Lean_Parser_ParserState_stackSize(x_5);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
x_16 = lean_nat_dec_eq(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Parser_ParserState_restore(x_5, x_2, x_3);
x_18 = l_Lean_Parser_ParserState_pushSyntax(x_17, x_1);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
x_20 = l_Lean_Parser_SyntaxStack_back(x_19);
lean_dec(x_19);
x_21 = l_Lean_Syntax_isAntiquots(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Parser_ParserState_restore(x_5, x_2, x_3);
x_23 = l_Lean_Parser_ParserState_pushSyntax(x_22, x_1);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = l_Lean_Parser_orelseFnCore___lambda__1(x_1, x_2, x_5, x_24);
return x_25;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_Parser_ParserState_restore(x_5, x_2, x_3);
x_27 = l_Lean_Parser_ParserState_pushSyntax(x_26, x_1);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Parser_orelseFnCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_9);
return x_10;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
x_10 = l_Lean_Parser_ParserState_restore(x_7, x_1, x_2);
x_11 = lean_apply_2(x_3, x_4, x_10);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Parser_ParserState_restore(x_11, x_1, x_9);
x_16 = l_Lean_Parser_ParserState_pushSyntax(x_15, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Parser_orelseFnCore___lambda__3(x_5, x_1, x_9, x_6, x_11, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Parser_ParserState_stackSize(x_5);
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
lean_inc(x_4);
x_8 = lean_apply_2(x_1, x_4, x_5);
x_9 = lean_ctor_get(x_8, 4);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = l_Lean_Parser_SyntaxStack_back(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = l___private_Lean_Parser_Basic_0__Lean_Parser_beqOrElseOnAntiquotBehavior____x40_Lean_Parser_Basic___hyg_665_(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = l_Lean_Parser_ParserState_stackSize(x_8);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_6, x_15);
x_17 = lean_nat_dec_eq(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
if (x_17 == 0)
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
else
{
uint8_t x_18; 
lean_inc(x_11);
x_18 = l_Lean_Syntax_isAntiquots(x_11);
if (x_18 == 0)
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_Parser_orelseFnCore___lambda__4(x_6, x_7, x_2, x_4, x_11, x_3, x_8, x_19);
lean_dec(x_6);
return x_20;
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_ctor_get(x_8, 2);
lean_inc(x_22);
x_23 = lean_nat_dec_eq(x_22, x_7);
lean_dec(x_22);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
lean_inc(x_7);
x_24 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
lean_dec(x_6);
x_25 = lean_apply_2(x_2, x_4, x_24);
x_26 = 1;
x_27 = l_Lean_Parser_mergeOrElseErrors(x_25, x_21, x_7, x_26);
lean_dec(x_7);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_orelseFnCore___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Parser_orelseFnCore___lambda__2(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Parser_orelseFnCore___lambda__3(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l_Lean_Parser_orelseFnCore___lambda__4(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
lean_dec(x_8);
lean_dec(x_1);
return x_10;
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
x_5 = 2;
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
static lean_object* _init_l___regBuiltin_Lean_Parser_orelse_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("orelse", 6, 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_orelse_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_orelse_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_orelse_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Run `p`, falling back to `q` if `p` failed without consuming any input.\n\nNOTE: In order for the pretty printer to retrace an `orelse`, `p` must be a call to `node` or some other parser\nproducing a single node kind. Nested `orelse` calls are flattened for this, i.e. `(node k1 p1 <|> node k2 p2) <|> ...`\nis fine as well. ", 321, 321);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_orelse_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_orelse_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_orelse_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelse___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 2;
x_6 = l_Lean_Parser_orelseFnCore(x_1, x_2, x_5, x_3, x_4);
return x_6;
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
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_orelse___elambda__1), 4, 2);
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_2, x_3);
x_5 = l_Lean_Parser_orelse(x_1, x_4);
return x_5;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_18 = x_6;
} else {
 lean_dec_ref(x_6);
 x_18 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(1, 1, 0);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_4);
lean_ctor_set(x_20, 3, x_15);
lean_ctor_set(x_20, 4, x_19);
lean_ctor_set(x_20, 5, x_16);
return x_20;
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_atomic_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("atomic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_atomic_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_atomic_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_atomic_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The `atomic(p)` parser parses `p`, returns the same result as `p` and fails iff `p` fails,\nbut if `p` fails after consuming some tokens `atomic(p)` will fail without consuming tokens.\nThis is important for the `p <|> q` combinator, because it is not backtracking, and will fail if\n`p` fails after consuming some tokens. To get backtracking behavior, use `atomic(p) <|> q` instead.\n\nThis parser has the same arity as `p` - it produces the same result as `p`. ", 458, 458);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_atomic_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_atomic_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_atomic_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomic___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_atomicFn(x_1, x_2, x_3);
return x_4;
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
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_atomic___elambda__1), 3, 1);
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
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_atomic___elambda__1), 3, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqRecoveryContext____x40_Lean_Parser_Basic___hyg_1255_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_nat_dec_eq(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_4, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqRecoveryContext____x40_Lean_Parser_Basic___hyg_1255____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Parser_Basic_0__Lean_Parser_beqRecoveryContext____x40_Lean_Parser_Basic___hyg_1255_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_instBEqRecoveryContext___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_beqRecoveryContext____x40_Lean_Parser_Basic___hyg_1255____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instBEqRecoveryContext() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instBEqRecoveryContext___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_decEqRecoveryContext____x40_Lean_Parser_Basic___hyg_1329_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_nat_dec_eq(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_4, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decEqRecoveryContext____x40_Lean_Parser_Basic___hyg_1329____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Parser_Basic_0__Lean_Parser_decEqRecoveryContext____x40_Lean_Parser_Basic___hyg_1329_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Parser_Basic_0__Lean_Parser_decEqRecoveryContext____x40_Lean_Parser_Basic___hyg_1329_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_instDecidableEqRecoveryContext(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initialPos", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__3;
x_2 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__5;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(14u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ byteIdx := ", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initialSize", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__14;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(15u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__17;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__18;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__17;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__9;
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__11;
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__7;
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = 0;
x_13 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__6;
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__13;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__15;
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__5;
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l___private_Init_Data_Repr_0__Nat_reprFast(x_24);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__16;
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_12);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__20;
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_8);
x_34 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__19;
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_12);
return x_36;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instReprRecoveryContext___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recoverFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = l_Lean_Parser_SyntaxStack_size(x_6);
lean_dec(x_6);
lean_inc(x_3);
x_8 = lean_apply_2(x_1, x_3, x_4);
x_9 = lean_ctor_get(x_8, 4);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_11 = lean_ctor_get(x_8, 4);
lean_dec(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_box(0);
lean_ctor_set(x_8, 4, x_14);
x_15 = lean_apply_3(x_2, x_13, x_3, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 4);
lean_inc(x_20);
x_21 = lean_ctor_get(x_15, 5);
lean_inc(x_21);
x_22 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_20, x_14);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
return x_15;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_15, 5);
lean_dec(x_24);
x_25 = lean_ctor_get(x_15, 4);
lean_dec(x_25);
x_26 = lean_ctor_get(x_15, 3);
lean_dec(x_26);
x_27 = lean_ctor_get(x_15, 2);
lean_dec(x_27);
x_28 = lean_ctor_get(x_15, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_15, 0);
lean_dec(x_29);
lean_inc(x_16);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_12);
lean_inc(x_18);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_push(x_21, x_31);
lean_ctor_set(x_15, 5, x_32);
lean_ctor_set(x_15, 4, x_14);
return x_15;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_15);
lean_inc(x_16);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_16);
lean_ctor_set(x_33, 1, x_12);
lean_inc(x_18);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_18);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_array_push(x_21, x_34);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_16);
lean_ctor_set(x_36, 1, x_17);
lean_ctor_set(x_36, 2, x_18);
lean_ctor_set(x_36, 3, x_19);
lean_ctor_set(x_36, 4, x_14);
lean_ctor_set(x_36, 5, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_8, 0);
x_38 = lean_ctor_get(x_8, 1);
x_39 = lean_ctor_get(x_8, 2);
x_40 = lean_ctor_get(x_8, 3);
x_41 = lean_ctor_get(x_8, 5);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_8);
x_42 = lean_ctor_get(x_9, 0);
lean_inc(x_42);
lean_dec(x_9);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_5);
lean_ctor_set(x_43, 1, x_7);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_38);
lean_ctor_set(x_45, 2, x_39);
lean_ctor_set(x_45, 3, x_40);
lean_ctor_set(x_45, 4, x_44);
lean_ctor_set(x_45, 5, x_41);
x_46 = lean_apply_3(x_2, x_43, x_3, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_46, 4);
lean_inc(x_51);
x_52 = lean_ctor_get(x_46, 5);
lean_inc(x_52);
x_53 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_51, x_44);
if (x_53 == 0)
{
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_42);
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 lean_ctor_release(x_46, 4);
 lean_ctor_release(x_46, 5);
 x_54 = x_46;
} else {
 lean_dec_ref(x_46);
 x_54 = lean_box(0);
}
lean_inc(x_47);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_42);
lean_inc(x_49);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_array_push(x_52, x_56);
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(0, 6, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_47);
lean_ctor_set(x_58, 1, x_48);
lean_ctor_set(x_58, 2, x_49);
lean_ctor_set(x_58, 3, x_50);
lean_ctor_set(x_58, 4, x_44);
lean_ctor_set(x_58, 5, x_57);
return x_58;
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("recover'", 8, 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Recover from errors in `parser` using `handler` to consume input until a known-good state has appeared.\nIf `handler` fails itself, then no recovery is performed.\n\n`handler` is provided with information about the failing parser's effects , and it is run in the\nstate immediately after the failure.\n\nThe interactions between <|> and `recover'` are subtle, especially for syntactic\ncategories that admit user extension. Consider avoiding it in these cases. ", 454, 454);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_recover_x27_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_recoverFn(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_apply_1(x_1, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_recover_x27___lambda__1), 4, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_recover_x27___elambda__1), 4, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_recover_x27___lambda__1), 4, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_recover_x27___elambda__1), 4, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_recover_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("recover", 7, 7);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_recover_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_recover_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_recover_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Recover from errors in `parser` using `handler` to consume input until a known-good state has appeared.\nIf `handler` fails itself, then no recovery is performed.\n\n`handler` is run in the state immediately after the failure.\n\nThe interactions between <|> and `recover` are subtle, especially for syntactic\ncategories that admit user extension. Consider avoiding it in these cases. ", 380, 380);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_recover_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_recover_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_recover_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_dbgTraceStateFn___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_recover_x27(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_optionalFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_optionalFn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_optionalFn___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l_Lean_Parser_ParserState_stackSize(x_3);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_apply_2(x_1, x_2, x_3);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 2);
lean_inc(x_10);
x_11 = lean_nat_dec_eq(x_10, x_5);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = l_Lean_Parser_optionalFn___closed__2;
x_13 = l_Lean_Parser_ParserState_mkNode(x_6, x_12, x_4);
lean_dec(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
x_15 = l_Lean_Parser_optionalFn___closed__2;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_4);
lean_dec(x_4);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_17 = l_Lean_Parser_optionalFn___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_6, x_17, x_4);
lean_dec(x_4);
return x_18;
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
LEAN_EXPORT lean_object* l_Lean_Parser_optionalNoAntiquot___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_optionalFn(x_1, x_2, x_3);
return x_4;
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
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_optionalNoAntiquot___elambda__1), 3, 1);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l_Lean_Parser_ParserState_stackSize(x_3);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_apply_2(x_1, x_2, x_3);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_10; 
x_10 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
lean_dec(x_4);
return x_10;
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lookahead", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_lookahead_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`lookahead(p)` runs `p` and fails if `p` does, but it produces no parse nodes and rewinds the\nposition to the original state on success. So for example `lookahead(\"=>\")` will ensure that the\nnext token is `\"=>\"`, without actually consuming this token.\n\nThis parser has arity 0 - it does not capture anything. ", 309, 309);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_lookahead_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_lookahead_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_lookaheadFn(x_1, x_2, x_3);
return x_4;
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
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_lookahead___elambda__1), 3, 1);
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
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_lookahead___elambda__1), 3, 1);
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
x_1 = lean_mk_string_unchecked("unexpected ", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = l_Lean_Parser_ParserState_stackSize(x_4);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_apply_2(x_1, x_3, x_4);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Parser_ParserState_restore(x_7, x_5, x_6);
lean_dec(x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_12 = l_Lean_Parser_ParserState_restore(x_7, x_5, x_6);
lean_dec(x_5);
x_13 = l_Lean_Parser_notFollowedByFn___closed__1;
x_14 = lean_string_append(x_13, x_2);
x_15 = l_Lean_Parser_dbgTraceStateFn___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_box(0);
x_18 = 1;
x_19 = l_Lean_Parser_ParserState_mkUnexpectedError(x_12, x_16, x_17, x_18);
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
static lean_object* _init_l___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("notFollowedBy", 13, 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`notFollowedBy(p, \"foo\")` succeeds iff `p` fails;\nif `p` succeeds then it fails with the message `\"unexpected foo\"`.\n\nThis parser has arity 0 - it does not capture anything. ", 174, 174);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_notFollowedBy_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_notFollowedByFn(x_2, x_1, x_3, x_4);
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
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedBy___elambda__1___boxed), 4, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = l_Lean_Parser_errorAtSavedPos___closed__2;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_notFollowedBy___elambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
x_8 = l_Lean_Parser_ParserState_stackSize(x_4);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Parser_manyAux(x_1, x_2, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Parser_optionalFn___closed__2;
x_12 = l_Lean_Parser_ParserState_mkNode(x_4, x_11, x_3);
x_13 = l_Lean_Parser_manyAux(x_1, x_2, x_12);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Parser_manyAux___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid 'many' parser combinator application, parser did not consume anything", 77, 77);
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
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Parser_manyAux___lambda__2(x_1, x_2, x_3, x_5, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_Parser_manyAux___lambda__3___closed__1;
x_13 = 1;
x_14 = l_Lean_Parser_ParserState_mkUnexpectedError(x_5, x_12, x_11, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l_Lean_Parser_ParserState_stackSize(x_3);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_2);
x_6 = lean_apply_2(x_1, x_2, x_3);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_ctor_get(x_6, 2);
lean_inc(x_10);
x_11 = lean_nat_dec_eq(x_5, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
lean_dec(x_4);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Parser_manyAux___lambda__3(x_1, x_2, x_4, x_5, x_6, x_13);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
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
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Parser_manyAux___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Parser_ParserState_stackSize(x_3);
x_5 = l_Lean_Parser_manyAux(x_1, x_2, x_3);
x_6 = l_Lean_Parser_optionalFn___closed__2;
x_7 = l_Lean_Parser_ParserState_mkNode(x_5, x_6, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyNoAntiquot___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_manyFn(x_1, x_2, x_3);
return x_4;
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
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_manyNoAntiquot___elambda__1), 3, 1);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Parser_ParserState_stackSize(x_3);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_manyAux), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_Parser_andthenFn(x_1, x_5, x_2, x_3);
x_7 = l_Lean_Parser_optionalFn___closed__2;
x_8 = l_Lean_Parser_ParserState_mkNode(x_6, x_7, x_4);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1NoAntiquot___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_many1Fn(x_1, x_2, x_3);
return x_4;
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
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_many1NoAntiquot___elambda__1), 3, 1);
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
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_many1NoAntiquot___elambda__1), 3, 1);
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
x_8 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(x_1, x_2, x_3, x_4, x_3, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_6, x_9);
x_11 = l_Lean_Parser_ParserState_stackSize(x_7);
x_12 = lean_nat_dec_lt(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(x_1, x_2, x_3, x_4, x_3, x_5, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Parser_optionalFn___closed__2;
x_15 = l_Lean_Parser_ParserState_mkNode(x_7, x_14, x_6);
x_16 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(x_1, x_2, x_3, x_4, x_3, x_5, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = l_Lean_Parser_ParserState_stackSize(x_6);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
lean_inc(x_1);
lean_inc(x_2);
x_10 = lean_apply_2(x_1, x_2, x_6);
x_11 = lean_ctor_get(x_10, 4);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Parser_ParserState_restore(x_10, x_8, x_9);
lean_dec(x_8);
x_15 = l_Lean_Parser_optionalFn___closed__2;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
x_17 = lean_box(0);
x_18 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__2(x_3, x_1, x_4, x_5, x_2, x_8, x_10, x_17);
lean_dec(x_8);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_6, x_9);
x_11 = l_Lean_Parser_ParserState_stackSize(x_7);
x_12 = lean_nat_dec_lt(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__3(x_1, x_2, x_3, x_4, x_5, x_7, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_Parser_optionalFn___closed__2;
x_16 = l_Lean_Parser_ParserState_mkNode(x_7, x_15, x_6);
x_17 = lean_box(0);
x_18 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__3(x_1, x_2, x_3, x_4, x_5, x_16, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = l_Lean_Parser_ParserState_stackSize(x_7);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_inc(x_1);
lean_inc(x_6);
x_10 = lean_apply_2(x_1, x_6, x_7);
x_11 = lean_ctor_get(x_10, 4);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_ctor_get(x_10, 2);
lean_inc(x_14);
x_15 = lean_nat_dec_lt(x_9, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
if (x_5 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
x_16 = lean_box(0);
x_17 = l_Lean_Parser_ParserState_pushSyntax(x_10, x_16);
x_18 = l_Lean_Parser_optionalFn___closed__2;
x_19 = l_Lean_Parser_ParserState_mkNode(x_17, x_18, x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_Parser_ParserState_restore(x_10, x_8, x_9);
lean_dec(x_8);
x_21 = l_Lean_Parser_optionalFn___closed__2;
x_22 = l_Lean_Parser_ParserState_mkNode(x_20, x_21, x_4);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_8);
x_23 = l_Lean_Parser_optionalFn___closed__2;
x_24 = l_Lean_Parser_ParserState_mkNode(x_10, x_23, x_4);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
x_25 = lean_box(0);
x_26 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___lambda__4(x_2, x_6, x_1, x_3, x_4, x_8, x_10, x_25);
lean_dec(x_8);
return x_26;
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
lean_dec(x_7);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_4);
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
lean_dec(x_7);
lean_dec(x_5);
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
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_4);
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
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_ParserState_stackSize(x_5);
x_7 = 1;
x_8 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(x_2, x_3, x_1, x_6, x_7, x_4, x_5);
lean_dec(x_6);
return x_8;
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
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = l_Lean_Parser_ParserState_stackSize(x_5);
x_7 = 0;
x_8 = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(x_2, x_3, x_1, x_6, x_7, x_4, x_5);
lean_dec(x_6);
return x_8;
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
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot___elambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_sepByFn(x_1, x_2, x_3, x_4, x_5);
return x_6;
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
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_sepByNoAntiquot___elambda__1___boxed), 5, 3);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Parser_sepByNoAntiquot___elambda__1(x_6, x_2, x_3, x_4, x_5);
return x_7;
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
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot___elambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_sepBy1Fn(x_1, x_2, x_3, x_4, x_5);
return x_6;
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
x_10 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1NoAntiquot___elambda__1___boxed), 5, 3);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Parser_sepBy1NoAntiquot___elambda__1(x_6, x_2, x_3, x_4, x_5);
return x_7;
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
x_8 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_6, x_7);
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
x_10 = l_Lean_Parser_SyntaxStack_back(x_9);
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOf___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_withResultOfFn(x_2, x_1, x_3, x_4);
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
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_withResultOf___elambda__1), 4, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_5);
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_many1NoAntiquot(x_1);
x_3 = l_Lean_Parser_many1Unbox___closed__1;
x_4 = l_Lean_Parser_withResultOf(x_2, x_3);
return x_4;
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
static lean_object* _init_l_Lean_Parser_satisfyFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
return x_1;
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
x_9 = lean_string_utf8_get_fast(x_7, x_5);
x_10 = lean_box_uint32(x_9);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = 1;
x_15 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_2, x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = l_Lean_Parser_ParserState_next_x27(x_4, x_7, x_5, lean_box(0));
lean_dec(x_5);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = l_Lean_Parser_satisfyFn___closed__1;
x_19 = 1;
x_20 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_18, x_17, x_19);
return x_20;
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
x_8 = lean_string_utf8_get_fast(x_6, x_4);
x_9 = lean_box_uint32(x_8);
lean_inc(x_1);
x_10 = lean_apply_1(x_1, x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Parser_ParserState_next_x27(x_3, x_6, x_4, lean_box(0));
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___boxed), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_Parser_andthenFn(x_5, x_6, x_3, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_finishCommentBlock_eoi___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unterminated comment", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock_eoi(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_Lean_Parser_finishCommentBlock_eoi___closed__1;
x_5 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_4, x_3, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock_eoi___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Parser_finishCommentBlock_eoi(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_string_utf8_at_end(x_6, x_7);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get_fast(x_6, x_7);
x_10 = lean_string_utf8_next_fast(x_6, x_7);
lean_dec(x_7);
x_11 = 45;
x_12 = lean_uint32_dec_eq(x_9, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 47;
x_14 = lean_uint32_dec_eq(x_9, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Parser_ParserState_setPos(x_4, x_10);
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
x_17 = lean_string_utf8_at_end(x_6, x_10);
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; 
x_18 = lean_string_utf8_get_fast(x_6, x_10);
x_19 = lean_uint32_dec_eq(x_18, x_11);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_Lean_Parser_ParserState_setPos(x_4, x_10);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
lean_dec(x_2);
x_24 = l_Lean_Parser_ParserState_next_x27(x_4, x_6, x_10, lean_box(0));
lean_dec(x_10);
x_2 = x_23;
x_4 = x_24;
goto _start;
}
}
else
{
lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_2);
x_26 = l_Lean_Parser_finishCommentBlock_eoi(x_1, x_4);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = lean_string_utf8_at_end(x_6, x_10);
if (x_27 == 0)
{
uint32_t x_28; uint32_t x_29; uint8_t x_30; 
x_28 = lean_string_utf8_get_fast(x_6, x_10);
x_29 = 47;
x_30 = lean_uint32_dec_eq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_Parser_ParserState_setPos(x_4, x_10);
x_4 = x_31;
goto _start;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_dec_eq(x_2, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_nat_sub(x_2, x_33);
lean_dec(x_2);
x_36 = l_Lean_Parser_ParserState_next_x27(x_4, x_6, x_10, lean_box(0));
lean_dec(x_10);
x_2 = x_35;
x_4 = x_36;
goto _start;
}
else
{
lean_object* x_38; 
lean_dec(x_2);
x_38 = l_Lean_Parser_ParserState_next_x27(x_4, x_6, x_10, lean_box(0));
lean_dec(x_10);
return x_38;
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_10);
lean_dec(x_2);
x_39 = l_Lean_Parser_finishCommentBlock_eoi(x_1, x_4);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_7);
lean_dec(x_2);
x_40 = l_Lean_Parser_finishCommentBlock_eoi(x_1, x_4);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Parser_finishCommentBlock(x_5, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_whitespace___lambda__1(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint32_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_whitespace___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_box(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_finishCommentBlock___boxed), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_whitespace___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_whitespace___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isolated carriage returns are not allowed", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_whitespace___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tabs are not allowed; please configure your editor to expand them", 65, 65);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_whitespace___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace(lean_object* x_1, lean_object* x_2) {
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
if (x_6 == 0)
{
uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_7 = lean_string_utf8_get_fast(x_4, x_5);
x_8 = 9;
x_9 = lean_uint32_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 13;
x_11 = lean_uint32_dec_eq(x_7, x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 32;
x_13 = lean_uint32_dec_eq(x_7, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 10;
x_15 = lean_uint32_dec_eq(x_7, x_14);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 45;
x_17 = lean_uint32_dec_eq(x_7, x_16);
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; 
x_18 = 47;
x_19 = lean_uint32_dec_eq(x_7, x_18);
if (x_19 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_20; uint32_t x_21; uint8_t x_22; 
x_20 = lean_string_utf8_next_fast(x_4, x_5);
lean_dec(x_5);
x_21 = lean_string_utf8_get(x_4, x_20);
x_22 = lean_uint32_dec_eq(x_21, x_16);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_23; uint32_t x_24; uint8_t x_25; 
x_23 = lean_string_utf8_next(x_4, x_20);
lean_dec(x_20);
x_24 = lean_string_utf8_get(x_4, x_23);
x_25 = lean_uint32_dec_eq(x_24, x_16);
if (x_25 == 0)
{
uint32_t x_26; uint8_t x_27; 
x_26 = 33;
x_27 = lean_uint32_dec_eq(x_24, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = l_Lean_Parser_ParserState_next(x_2, x_4, x_23);
lean_dec(x_23);
lean_dec(x_4);
x_29 = l_Lean_Parser_whitespace___closed__1;
x_30 = l_Lean_Parser_whitespace___closed__2;
x_31 = l_Lean_Parser_andthenFn(x_29, x_30, x_1, x_28);
return x_31;
}
else
{
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
}
else
{
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
}
}
}
else
{
lean_object* x_32; uint32_t x_33; uint8_t x_34; 
x_32 = lean_string_utf8_next_fast(x_4, x_5);
lean_dec(x_5);
x_33 = lean_string_utf8_get(x_4, x_32);
x_34 = lean_uint32_dec_eq(x_33, x_16);
if (x_34 == 0)
{
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = l_Lean_Parser_whitespace___boxed__const__1;
x_36 = lean_alloc_closure((void*)(l_Lean_Parser_whitespace___lambda__1___boxed), 2, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = lean_alloc_closure((void*)(l_Lean_Parser_takeUntilFn___boxed), 3, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = l_Lean_Parser_ParserState_next(x_2, x_4, x_32);
lean_dec(x_32);
lean_dec(x_4);
x_39 = l_Lean_Parser_whitespace___closed__2;
x_40 = l_Lean_Parser_andthenFn(x_37, x_39, x_1, x_38);
return x_40;
}
}
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Parser_ParserState_next_x27(x_2, x_4, x_5, lean_box(0));
lean_dec(x_5);
lean_dec(x_4);
x_2 = x_41;
goto _start;
}
}
else
{
lean_object* x_43; 
x_43 = l_Lean_Parser_ParserState_next_x27(x_2, x_4, x_5, lean_box(0));
lean_dec(x_5);
lean_dec(x_4);
x_2 = x_43;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = l_Lean_Parser_whitespace___closed__3;
x_47 = 0;
x_48 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_46, x_45, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_49 = lean_box(0);
x_50 = l_Lean_Parser_whitespace___closed__4;
x_51 = 0;
x_52 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_50, x_49, x_51);
return x_52;
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
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Lean_Parser_whitespace___lambda__1(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
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
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 2);
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
lean_inc_n(x_1, 2);
lean_inc(x_7);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 1, x_1);
x_11 = lean_string_utf8_extract(x_7, x_1, x_10);
if (x_2 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_inc(x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_10);
x_13 = lean_string_utf8_byte_size(x_11);
x_14 = lean_nat_add(x_1, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_1);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_14);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
x_17 = l_Lean_Parser_ParserState_pushSyntax(x_4, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = l_Lean_Parser_whitespace(x_3, x_4);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_string_utf8_byte_size(x_11);
x_22 = lean_nat_add(x_1, x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_1);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_22);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_11);
x_25 = l_Lean_Parser_ParserState_pushSyntax(x_18, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_ctor_get(x_4, 2);
lean_inc(x_27);
lean_inc_n(x_1, 2);
lean_inc(x_26);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_1);
lean_ctor_set(x_28, 2, x_1);
x_29 = lean_string_utf8_extract(x_26, x_1, x_27);
if (x_2 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_3);
lean_inc(x_27);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_27);
x_31 = lean_string_utf8_byte_size(x_29);
x_32 = lean_nat_add(x_1, x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_1);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_32);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
x_35 = l_Lean_Parser_ParserState_pushSyntax(x_4, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = l_Lean_Parser_whitespace(x_3, x_4);
x_37 = lean_ctor_get(x_36, 2);
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_27);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_string_utf8_byte_size(x_29);
x_40 = lean_nat_add(x_1, x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_1);
lean_ctor_set(x_41, 2, x_38);
lean_ctor_set(x_41, 3, x_40);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_29);
x_43 = l_Lean_Parser_ParserState_pushSyntax(x_36, x_42);
return x_43;
}
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
x_9 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
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
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn(uint32_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_box_uint32(x_1);
x_6 = lean_alloc_closure((void*)(l_UInt32_decEq___boxed), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = l_Lean_Parser_dbgTraceStateFn___closed__1;
x_8 = lean_string_push(x_7, x_1);
x_9 = l_Lean_Parser_chFn___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_string_append(x_10, x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(x_12, 0, x_6);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_rawFn(x_12, x_2, x_3, x_4);
return x_13;
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
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___elambda__1(uint32_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_chFn(x_1, x_2, x_3, x_4);
return x_5;
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
x_1 = lean_mk_string_unchecked("invalid hexadecimal numeral", 27, 27);
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
uint32_t x_7; lean_object* x_8; lean_object* x_9; uint32_t x_24; uint8_t x_25; 
x_7 = lean_string_utf8_get_fast(x_4, x_5);
x_8 = lean_string_utf8_next_fast(x_4, x_5);
lean_dec(x_5);
x_24 = 48;
x_25 = lean_uint32_dec_le(x_24, x_7);
if (x_25 == 0)
{
uint32_t x_26; uint8_t x_27; 
x_26 = 97;
x_27 = lean_uint32_dec_le(x_26, x_7);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_box(0);
x_9 = x_28;
goto block_23;
}
else
{
uint32_t x_29; uint8_t x_30; 
x_29 = 102;
x_30 = lean_uint32_dec_le(x_7, x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_box(0);
x_9 = x_31;
goto block_23;
}
else
{
lean_object* x_32; 
x_32 = l_Lean_Parser_ParserState_setPos(x_2, x_8);
return x_32;
}
}
}
else
{
uint32_t x_33; uint8_t x_34; 
x_33 = 57;
x_34 = lean_uint32_dec_le(x_7, x_33);
if (x_34 == 0)
{
uint32_t x_35; uint8_t x_36; 
x_35 = 97;
x_36 = lean_uint32_dec_le(x_35, x_7);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_box(0);
x_9 = x_37;
goto block_23;
}
else
{
uint32_t x_38; uint8_t x_39; 
x_38 = 102;
x_39 = lean_uint32_dec_le(x_7, x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_box(0);
x_9 = x_40;
goto block_23;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Parser_ParserState_setPos(x_2, x_8);
return x_41;
}
}
}
else
{
lean_object* x_42; 
x_42 = l_Lean_Parser_ParserState_setPos(x_2, x_8);
return x_42;
}
}
block_23:
{
uint32_t x_10; uint8_t x_11; 
lean_dec(x_9);
x_10 = 65;
x_11 = lean_uint32_dec_le(x_10, x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = l_Lean_Parser_hexDigitFn___closed__1;
x_14 = 1;
x_15 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_13, x_12, x_14);
return x_15;
}
else
{
uint32_t x_16; uint8_t x_17; 
x_16 = 70;
x_17 = lean_uint32_dec_le(x_7, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = l_Lean_Parser_hexDigitFn___closed__1;
x_20 = 1;
x_21 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_19, x_18, x_20);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = l_Lean_Parser_ParserState_setPos(x_2, x_8);
return x_22;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
lean_dec(x_5);
x_43 = lean_box(0);
x_44 = l_Lean_Parser_satisfyFn___closed__1;
x_45 = 1;
x_46 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_44, x_43, x_45);
return x_46;
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
static lean_object* _init_l_Lean_Parser_stringGapFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expecting newline in string gap", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_stringGapFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected additional newline in string gap", 43, 43);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
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
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_6, x_4);
x_9 = 10;
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 32;
x_12 = lean_uint32_dec_eq(x_8, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 9;
x_14 = lean_uint32_dec_eq(x_8, x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 13;
x_16 = lean_uint32_dec_eq(x_8, x_15);
if (x_16 == 0)
{
lean_dec(x_4);
if (x_1 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_box(0);
x_18 = l_Lean_Parser_stringGapFn___closed__1;
x_19 = 1;
x_20 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_18, x_17, x_19);
return x_20;
}
else
{
return x_3;
}
}
else
{
lean_object* x_21; 
x_21 = l_Lean_Parser_ParserState_next_x27(x_3, x_6, x_4, lean_box(0));
lean_dec(x_4);
x_3 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; 
x_23 = l_Lean_Parser_ParserState_next_x27(x_3, x_6, x_4, lean_box(0));
lean_dec(x_4);
x_3 = x_23;
goto _start;
}
}
else
{
lean_object* x_25; 
x_25 = l_Lean_Parser_ParserState_next_x27(x_3, x_6, x_4, lean_box(0));
lean_dec(x_4);
x_3 = x_25;
goto _start;
}
}
else
{
if (x_1 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Parser_ParserState_next_x27(x_3, x_6, x_4, lean_box(0));
lean_dec(x_4);
x_28 = 1;
x_1 = x_28;
x_3 = x_27;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = l_Lean_Parser_stringGapFn___closed__2;
x_32 = 1;
x_33 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_31, x_30, x_32);
return x_33;
}
}
}
else
{
lean_dec(x_4);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Parser_stringGapFn(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharCoreFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid escape sequence", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharCoreFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharCoreFn___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_quotedCharCoreFn___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharCoreFn___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_quotedCharCoreFn___closed__2;
x_2 = l_Lean_Parser_quotedCharCoreFn___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_string_utf8_at_end(x_6, x_7);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get_fast(x_6, x_7);
x_10 = lean_box_uint32(x_9);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 120;
x_14 = lean_uint32_dec_eq(x_9, x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 117;
x_16 = lean_uint32_dec_eq(x_9, x_15);
if (x_16 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
if (x_2 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = l_Lean_Parser_quotedCharCoreFn___closed__1;
x_19 = 1;
x_20 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_18, x_17, x_19);
return x_20;
}
else
{
uint32_t x_21; uint8_t x_22; 
x_21 = 10;
x_22 = lean_uint32_dec_eq(x_9, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = l_Lean_Parser_quotedCharCoreFn___closed__1;
x_25 = 1;
x_26 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_24, x_23, x_25);
return x_26;
}
else
{
uint8_t x_27; lean_object* x_28; 
x_27 = 0;
x_28 = l_Lean_Parser_stringGapFn(x_27, x_3, x_4);
lean_dec(x_3);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = l_Lean_Parser_ParserState_next_x27(x_4, x_6, x_7, lean_box(0));
lean_dec(x_7);
lean_dec(x_6);
x_30 = l_Lean_Parser_quotedCharCoreFn___closed__2;
x_31 = l_Lean_Parser_quotedCharCoreFn___closed__4;
x_32 = l_Lean_Parser_andthenFn(x_30, x_31, x_3, x_29);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Lean_Parser_ParserState_next_x27(x_4, x_6, x_7, lean_box(0));
lean_dec(x_7);
lean_dec(x_6);
x_34 = l_Lean_Parser_quotedCharCoreFn___closed__2;
x_35 = l_Lean_Parser_andthenFn(x_34, x_34, x_3, x_33);
return x_35;
}
}
else
{
lean_object* x_36; 
lean_dec(x_3);
x_36 = l_Lean_Parser_ParserState_next_x27(x_4, x_6, x_7, lean_box(0));
lean_dec(x_7);
lean_dec(x_6);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_box(0);
x_38 = l_Lean_Parser_satisfyFn___closed__1;
x_39 = 1;
x_40 = l_Lean_Parser_ParserState_mkUnexpectedError(x_4, x_38, x_37, x_39);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Parser_quotedCharCoreFn(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 92;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 34;
x_5 = lean_uint32_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 39;
x_7 = lean_uint32_dec_eq(x_1, x_6);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 114;
x_9 = lean_uint32_dec_eq(x_1, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 110;
x_11 = lean_uint32_dec_eq(x_1, x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 116;
x_13 = lean_uint32_dec_eq(x_1, x_12);
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
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = l_Lean_Parser_quotedCharFn___closed__1;
x_4 = 0;
x_5 = l_Lean_Parser_quotedCharCoreFn(x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedStringFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = l_Lean_Parser_quotedCharFn___closed__1;
x_4 = 1;
x_5 = l_Lean_Parser_quotedCharCoreFn(x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
lean_inc_n(x_3, 2);
lean_inc(x_8);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 1, x_3);
x_12 = lean_string_utf8_extract(x_8, x_3, x_11);
x_13 = l_Lean_Parser_whitespace(x_1, x_2);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_11);
x_17 = l_Lean_Syntax_mkLit(x_4, x_12, x_16);
x_18 = l_Lean_Parser_ParserState_pushSyntax(x_13, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
lean_inc_n(x_3, 2);
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_21, 2, x_3);
x_22 = lean_string_utf8_extract(x_19, x_3, x_20);
x_23 = l_Lean_Parser_whitespace(x_1, x_2);
x_24 = lean_ctor_get(x_23, 2);
lean_inc(x_24);
lean_inc(x_20);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set(x_26, 3, x_20);
x_27 = l_Lean_Syntax_mkLit(x_4, x_22, x_26);
x_28 = l_Lean_Parser_ParserState_pushSyntax(x_23, x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 4);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_5, x_6);
if (x_7 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Lean_Parser_mkNodeToken___lambda__1(x_3, x_4, x_2, x_1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_mkNodeToken___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_charLitFnAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("missing end of character literal", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_charLitFnAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("char", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_charLitFnAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_charLitFnAux___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; lean_object* x_13; 
x_8 = lean_string_utf8_get_fast(x_5, x_6);
x_9 = lean_string_utf8_next_fast(x_5, x_6);
lean_dec(x_6);
lean_inc(x_9);
lean_inc(x_3);
x_10 = l_Lean_Parser_ParserState_setPos(x_3, x_9);
x_11 = 92;
x_12 = lean_uint32_dec_eq(x_8, x_11);
x_13 = lean_box(0);
if (x_12 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_3, 4);
lean_inc(x_14);
lean_dec(x_3);
x_15 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_14, x_13);
if (x_15 == 0)
{
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
else
{
uint32_t x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; uint8_t x_20; 
x_16 = lean_string_utf8_get(x_5, x_9);
x_17 = lean_string_utf8_next(x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
x_18 = l_Lean_Parser_ParserState_setPos(x_10, x_17);
x_19 = 39;
x_20 = lean_uint32_dec_eq(x_16, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = l_Lean_Parser_charLitFnAux___closed__1;
x_23 = 1;
x_24 = l_Lean_Parser_ParserState_mkUnexpectedError(x_18, x_22, x_21, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Parser_charLitFnAux___closed__3;
x_26 = l_Lean_Parser_mkNodeToken(x_25, x_1, x_2, x_18);
return x_26;
}
}
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_9);
lean_dec(x_3);
x_27 = l_Lean_Parser_quotedCharFn___closed__1;
x_28 = 0;
lean_inc(x_2);
x_29 = l_Lean_Parser_quotedCharCoreFn(x_27, x_28, x_2, x_10);
x_30 = lean_ctor_get(x_29, 4);
lean_inc(x_30);
x_31 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_30, x_13);
if (x_31 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_29;
}
else
{
lean_object* x_32; uint32_t x_33; lean_object* x_34; lean_object* x_35; uint32_t x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_29, 2);
lean_inc(x_32);
x_33 = lean_string_utf8_get(x_5, x_32);
x_34 = lean_string_utf8_next(x_5, x_32);
lean_dec(x_32);
lean_dec(x_5);
x_35 = l_Lean_Parser_ParserState_setPos(x_29, x_34);
x_36 = 39;
x_37 = lean_uint32_dec_eq(x_33, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = l_Lean_Parser_charLitFnAux___closed__1;
x_40 = 1;
x_41 = l_Lean_Parser_ParserState_mkUnexpectedError(x_35, x_39, x_38, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Lean_Parser_charLitFnAux___closed__3;
x_43 = l_Lean_Parser_mkNodeToken(x_42, x_1, x_2, x_35);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_box(0);
x_45 = l_Lean_Parser_satisfyFn___closed__1;
x_46 = 1;
x_47 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_45, x_44, x_46);
return x_47;
}
}
}
static lean_object* _init_l_Lean_Parser_strLitFnAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_quotedStringFn), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_strLitFnAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("str", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_strLitFnAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_strLitFnAux___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_strLitFnAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unterminated string literal", 27, 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; 
x_8 = lean_string_utf8_get_fast(x_5, x_6);
x_9 = lean_string_utf8_next_fast(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_10 = l_Lean_Parser_ParserState_setPos(x_3, x_9);
x_11 = 34;
x_12 = lean_uint32_dec_eq(x_8, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 92;
x_14 = lean_uint32_dec_eq(x_8, x_13);
if (x_14 == 0)
{
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_strLitFnAux), 3, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = l_Lean_Parser_strLitFnAux___closed__1;
x_18 = l_Lean_Parser_andthenFn(x_17, x_16, x_2, x_10);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_Parser_strLitFnAux___closed__3;
x_20 = l_Lean_Parser_mkNodeToken(x_19, x_1, x_2, x_10);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_21 = l_Lean_Parser_strLitFnAux___closed__4;
x_22 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_3, x_21, x_1);
return x_22;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isRawStrLitStart(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_utf8_at_end(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint32_t x_5; uint8_t x_6; 
x_4 = lean_string_utf8_get_fast(x_1, x_2);
x_5 = 35;
x_6 = lean_uint32_dec_eq(x_4, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
lean_dec(x_2);
x_7 = 34;
x_8 = lean_uint32_dec_eq(x_4, x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_string_utf8_next_fast(x_1, x_2);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
}
else
{
uint8_t x_11; 
lean_dec(x_2);
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isRawStrLitStart___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_isRawStrLitStart(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unterminated raw string literal", 31, 31);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_errorUnterminated(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__1;
x_4 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_normalState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_string_utf8_at_end(x_6, x_7);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_9 = lean_string_utf8_get_fast(x_6, x_7);
x_10 = lean_string_utf8_next_fast(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
x_11 = l_Lean_Parser_ParserState_setPos(x_4, x_10);
x_12 = 34;
x_13 = lean_uint32_dec_eq(x_9, x_12);
if (x_13 == 0)
{
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_2, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Parser_rawStrLitFnAux_closingState(x_1, x_2, x_15, x_3, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Parser_strLitFnAux___closed__3;
x_19 = l_Lean_Parser_mkNodeToken(x_18, x_1, x_3, x_11);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_20 = l_Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__1;
x_21 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_4, x_20, x_1);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_closingState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint32_t x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_10 = lean_string_utf8_get_fast(x_7, x_8);
x_11 = lean_string_utf8_next_fast(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
x_12 = l_Lean_Parser_ParserState_setPos(x_5, x_11);
x_13 = 35;
x_14 = lean_uint32_dec_eq(x_10, x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
lean_dec(x_3);
x_15 = 34;
x_16 = lean_uint32_dec_eq(x_10, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Parser_rawStrLitFnAux_normalState(x_1, x_2, x_4, x_12);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_unsigned_to_nat(0u);
x_3 = x_18;
x_5 = x_12;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_22 = lean_nat_dec_eq(x_21, x_2);
if (x_22 == 0)
{
x_3 = x_21;
x_5 = x_12;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
x_24 = l_Lean_Parser_strLitFnAux___closed__3;
x_25 = l_Lean_Parser_mkNodeToken(x_24, x_1, x_4, x_12);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_26 = l_Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__1;
x_27 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_5, x_26, x_1);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_normalState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_rawStrLitFnAux_normalState(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_closingState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_rawStrLitFnAux_closingState(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux_initState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_string_utf8_at_end(x_6, x_7);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_9 = lean_string_utf8_get_fast(x_6, x_7);
x_10 = lean_string_utf8_next_fast(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
x_11 = l_Lean_Parser_ParserState_setPos(x_4, x_10);
x_12 = 35;
x_13 = lean_uint32_dec_eq(x_9, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 34;
x_15 = lean_uint32_dec_eq(x_9, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = l_Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__1;
x_17 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_11, x_16, x_1);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_Parser_rawStrLitFnAux_normalState(x_1, x_2, x_3, x_11);
lean_dec(x_2);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l_Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__1;
x_23 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_4, x_22, x_1);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Parser_rawStrLitFnAux_initState(x_1, x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_takeDigitsFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected character", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_string_utf8_at_end(x_7, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_10 = lean_string_utf8_get_fast(x_7, x_8);
x_11 = 95;
x_12 = lean_uint32_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_box_uint32(x_10);
lean_inc(x_1);
x_14 = lean_apply_1(x_1, x_13);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_8);
lean_dec(x_1);
if (x_3 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Parser_takeDigitsFn___closed__1;
x_19 = 1;
x_20 = l_Lean_Parser_ParserState_mkUnexpectedError(x_5, x_18, x_17, x_19);
return x_20;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Parser_ParserState_next_x27(x_5, x_7, x_8, lean_box(0));
lean_dec(x_8);
x_22 = 0;
x_3 = x_22;
x_5 = x_21;
goto _start;
}
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Parser_ParserState_next_x27(x_5, x_7, x_8, lean_box(0));
lean_dec(x_8);
x_25 = 1;
x_3 = x_25;
x_5 = x_24;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
if (x_3 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Parser_satisfyFn___closed__1;
x_30 = 1;
x_31 = l_Lean_Parser_ParserState_mkUnexpectedError(x_5, x_29, x_28, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Parser_takeDigitsFn(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_decimalNumberFn_parseOptExp___lambda__1(uint32_t x_1, uint32_t x_2, uint32_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_uint32_dec_le(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_uint32_dec_le(x_3, x_2);
return x_6;
}
}
}
static lean_object* _init_l_Lean_Parser_decimalNumberFn_parseOptExp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("missing exponent digits in scientific literal", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_decimalNumberFn_parseOptExp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decimal number", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_decimalNumberFn_parseOptExp___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 48;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_decimalNumberFn_parseOptExp___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 57;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint32_t x_38; uint32_t x_39; uint8_t x_40; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_38 = lean_string_utf8_get(x_4, x_5);
x_39 = 101;
x_40 = lean_uint32_dec_eq(x_38, x_39);
if (x_40 == 0)
{
uint32_t x_41; uint8_t x_42; 
x_41 = 69;
x_42 = lean_uint32_dec_eq(x_38, x_41);
if (x_42 == 0)
{
lean_dec(x_5);
return x_2;
}
else
{
lean_object* x_43; 
x_43 = lean_box(0);
x_6 = x_43;
goto block_37;
}
}
else
{
lean_object* x_44; 
x_44 = lean_box(0);
x_6 = x_44;
goto block_37;
}
block_37:
{
lean_object* x_7; uint32_t x_8; uint32_t x_9; uint8_t x_10; uint32_t x_11; lean_object* x_12; 
lean_dec(x_6);
x_7 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
x_8 = lean_string_utf8_get(x_4, x_7);
x_9 = 45;
x_10 = lean_uint32_dec_eq(x_8, x_9);
x_11 = 48;
if (x_10 == 0)
{
uint32_t x_33; uint8_t x_34; 
x_33 = 43;
x_34 = lean_uint32_dec_eq(x_8, x_33);
if (x_34 == 0)
{
x_12 = x_7;
goto block_32;
}
else
{
lean_object* x_35; 
x_35 = lean_string_utf8_next(x_4, x_7);
lean_dec(x_7);
x_12 = x_35;
goto block_32;
}
}
else
{
lean_object* x_36; 
x_36 = lean_string_utf8_next(x_4, x_7);
lean_dec(x_7);
x_12 = x_36;
goto block_32;
}
block_32:
{
uint32_t x_13; uint8_t x_14; 
x_13 = lean_string_utf8_get(x_4, x_12);
x_14 = lean_uint32_dec_le(x_11, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_Lean_Parser_decimalNumberFn_parseOptExp___closed__1;
x_17 = 1;
x_18 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_16, x_15, x_17);
return x_18;
}
else
{
uint32_t x_19; uint8_t x_20; 
x_19 = 57;
x_20 = lean_uint32_dec_le(x_13, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
lean_dec(x_12);
x_21 = lean_box(0);
x_22 = l_Lean_Parser_decimalNumberFn_parseOptExp___closed__1;
x_23 = 1;
x_24 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_22, x_21, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_25 = l_Lean_Parser_decimalNumberFn_parseOptExp___boxed__const__1;
x_26 = l_Lean_Parser_decimalNumberFn_parseOptExp___boxed__const__2;
x_27 = lean_alloc_closure((void*)(l_Lean_Parser_decimalNumberFn_parseOptExp___lambda__1___boxed), 3, 2);
lean_closure_set(x_27, 0, x_25);
lean_closure_set(x_27, 1, x_26);
x_28 = l_Lean_Parser_ParserState_setPos(x_2, x_12);
x_29 = l_Lean_Parser_decimalNumberFn_parseOptExp___closed__2;
x_30 = 0;
x_31 = l_Lean_Parser_takeDigitsFn(x_27, x_29, x_30, x_1, x_28);
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseOptExp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; uint32_t x_5; uint32_t x_6; uint8_t x_7; lean_object* x_8; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_6 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_7 = l_Lean_Parser_decimalNumberFn_parseOptExp___lambda__1(x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
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
static lean_object* _init_l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 48;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 57;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1___boxed__const__1;
x_2 = l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1___boxed__const__2;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_decimalNumberFn_parseOptExp___lambda__1___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
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
x_8 = lean_uint32_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_2;
}
else
{
lean_object* x_9; uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_9 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
x_10 = lean_string_utf8_get(x_4, x_9);
x_11 = 48;
x_12 = lean_uint32_dec_le(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Parser_ParserState_setPos(x_2, x_9);
return x_13;
}
else
{
uint32_t x_14; uint8_t x_15; 
x_14 = 57;
x_15 = lean_uint32_dec_le(x_10, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Parser_ParserState_setPos(x_2, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_17 = l_Lean_Parser_ParserState_setPos(x_2, x_9);
x_18 = l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1;
x_19 = l_Lean_Parser_decimalNumberFn_parseOptExp___closed__2;
x_20 = 0;
x_21 = l_Lean_Parser_takeDigitsFn(x_18, x_19, x_20, x_1, x_17);
return x_21;
}
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
static lean_object* _init_l_Lean_Parser_decimalNumberFn_parseScientific___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("scientific", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_decimalNumberFn_parseScientific___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_decimalNumberFn_parseScientific___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn_parseScientific(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Parser_decimalNumberFn_parseOptDot(x_2, x_3);
x_5 = l_Lean_Parser_decimalNumberFn_parseOptExp(x_2, x_4);
x_6 = l_Lean_Parser_decimalNumberFn_parseScientific___closed__2;
x_7 = l_Lean_Parser_mkNodeToken(x_6, x_1, x_2, x_5);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_decimalNumberFn___lambda__1(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 48;
x_3 = lean_uint32_dec_le(x_2, x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint32_t x_5; uint8_t x_6; 
x_5 = 57;
x_6 = lean_uint32_dec_le(x_1, x_5);
return x_6;
}
}
}
static lean_object* _init_l_Lean_Parser_decimalNumberFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_decimalNumberFn___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_decimalNumberFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("num", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_decimalNumberFn___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_decimalNumberFn___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lean_Parser_decimalNumberFn___closed__1;
x_5 = l_Lean_Parser_decimalNumberFn_parseOptExp___closed__2;
x_6 = 0;
x_7 = l_Lean_Parser_takeDigitsFn(x_4, x_5, x_6, x_2, x_3);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_string_utf8_at_end(x_9, x_10);
if (x_11 == 0)
{
uint32_t x_12; uint32_t x_13; uint8_t x_14; 
x_12 = lean_string_utf8_get_fast(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_13 = 46;
x_14 = lean_uint32_dec_eq(x_12, x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 101;
x_16 = lean_uint32_dec_eq(x_12, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 69;
x_18 = lean_uint32_dec_eq(x_12, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_Parser_decimalNumberFn___closed__3;
x_20 = l_Lean_Parser_mkNodeToken(x_19, x_1, x_2, x_7);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = l_Lean_Parser_decimalNumberFn_parseScientific(x_1, x_2, x_7);
return x_21;
}
}
else
{
lean_object* x_22; 
x_22 = l_Lean_Parser_decimalNumberFn_parseScientific(x_1, x_2, x_7);
return x_22;
}
}
else
{
lean_object* x_23; 
x_23 = l_Lean_Parser_decimalNumberFn_parseScientific(x_1, x_2, x_7);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
x_24 = l_Lean_Parser_decimalNumberFn___closed__3;
x_25 = l_Lean_Parser_mkNodeToken(x_24, x_1, x_2, x_7);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_decimalNumberFn___lambda__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_binNumberFn___lambda__1(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 48;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 49;
x_5 = lean_uint32_dec_eq(x_1, x_4);
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
x_1 = lean_mk_string_unchecked("binary number", 13, 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lean_Parser_binNumberFn___closed__1;
x_5 = l_Lean_Parser_binNumberFn___closed__2;
x_6 = 1;
x_7 = l_Lean_Parser_takeDigitsFn(x_4, x_5, x_6, x_2, x_3);
x_8 = l_Lean_Parser_decimalNumberFn___closed__3;
x_9 = l_Lean_Parser_mkNodeToken(x_8, x_1, x_2, x_7);
return x_9;
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
LEAN_EXPORT uint8_t l_Lean_Parser_octalNumberFn___lambda__1(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 48;
x_3 = lean_uint32_dec_le(x_2, x_1);
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
x_6 = lean_uint32_dec_le(x_1, x_5);
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
x_1 = lean_mk_string_unchecked("octal number", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lean_Parser_octalNumberFn___closed__1;
x_5 = l_Lean_Parser_octalNumberFn___closed__2;
x_6 = 1;
x_7 = l_Lean_Parser_takeDigitsFn(x_4, x_5, x_6, x_2, x_3);
x_8 = l_Lean_Parser_decimalNumberFn___closed__3;
x_9 = l_Lean_Parser_mkNodeToken(x_8, x_1, x_2, x_7);
return x_9;
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
LEAN_EXPORT uint8_t l_Lean_Parser_hexNumberFn___lambda__1(uint32_t x_1) {
_start:
{
lean_object* x_2; uint32_t x_19; uint8_t x_20; 
x_19 = 48;
x_20 = lean_uint32_dec_le(x_19, x_1);
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
x_23 = lean_uint32_dec_le(x_1, x_22);
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
x_4 = lean_uint32_dec_le(x_3, x_1);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 65;
x_6 = lean_uint32_dec_le(x_5, x_1);
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
x_9 = lean_uint32_dec_le(x_1, x_8);
return x_9;
}
}
else
{
uint32_t x_10; uint8_t x_11; 
x_10 = 102;
x_11 = lean_uint32_dec_le(x_1, x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 65;
x_13 = lean_uint32_dec_le(x_12, x_1);
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
x_16 = lean_uint32_dec_le(x_1, x_15);
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
x_1 = lean_mk_string_unchecked("hexadecimal number", 18, 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lean_Parser_hexNumberFn___closed__1;
x_5 = l_Lean_Parser_hexNumberFn___closed__2;
x_6 = 1;
x_7 = l_Lean_Parser_takeDigitsFn(x_4, x_5, x_6, x_2, x_3);
x_8 = l_Lean_Parser_decimalNumberFn___closed__3;
x_9 = l_Lean_Parser_mkNodeToken(x_8, x_1, x_2, x_7);
return x_9;
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
static lean_object* _init_l_Lean_Parser_numberFnAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("numeral", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux(lean_object* x_1, lean_object* x_2) {
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
if (x_6 == 0)
{
uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_7 = lean_string_utf8_get_fast(x_4, x_5);
x_8 = 48;
x_9 = lean_uint32_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_uint32_dec_le(x_8, x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = l_Lean_Parser_numberFnAux___closed__1;
x_12 = l_Lean_Parser_ParserState_mkError(x_2, x_11);
return x_12;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 57;
x_14 = lean_uint32_dec_le(x_7, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_15 = l_Lean_Parser_numberFnAux___closed__1;
x_16 = l_Lean_Parser_ParserState_mkError(x_2, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_4);
x_18 = l_Lean_Parser_decimalNumberFn(x_5, x_1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; uint32_t x_20; uint32_t x_21; uint8_t x_22; 
x_19 = lean_string_utf8_next_fast(x_4, x_5);
x_20 = lean_string_utf8_get(x_4, x_19);
x_21 = 98;
x_22 = lean_uint32_dec_eq(x_20, x_21);
if (x_22 == 0)
{
uint32_t x_23; uint8_t x_24; 
x_23 = 66;
x_24 = lean_uint32_dec_eq(x_20, x_23);
if (x_24 == 0)
{
uint32_t x_25; uint8_t x_26; 
x_25 = 111;
x_26 = lean_uint32_dec_eq(x_20, x_25);
if (x_26 == 0)
{
uint32_t x_27; uint8_t x_28; 
x_27 = 79;
x_28 = lean_uint32_dec_eq(x_20, x_27);
if (x_28 == 0)
{
uint32_t x_29; uint8_t x_30; 
x_29 = 120;
x_30 = lean_uint32_dec_eq(x_20, x_29);
if (x_30 == 0)
{
uint32_t x_31; uint8_t x_32; 
x_31 = 88;
x_32 = lean_uint32_dec_eq(x_20, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
x_33 = l_Lean_Parser_ParserState_setPos(x_2, x_19);
x_34 = l_Lean_Parser_decimalNumberFn(x_5, x_1, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_Parser_ParserState_next(x_2, x_4, x_19);
lean_dec(x_19);
lean_dec(x_4);
x_36 = l_Lean_Parser_hexNumberFn(x_5, x_1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_Parser_ParserState_next(x_2, x_4, x_19);
lean_dec(x_19);
lean_dec(x_4);
x_38 = l_Lean_Parser_hexNumberFn(x_5, x_1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_Parser_ParserState_next(x_2, x_4, x_19);
lean_dec(x_19);
lean_dec(x_4);
x_40 = l_Lean_Parser_octalNumberFn(x_5, x_1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_Parser_ParserState_next(x_2, x_4, x_19);
lean_dec(x_19);
lean_dec(x_4);
x_42 = l_Lean_Parser_octalNumberFn(x_5, x_1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Lean_Parser_ParserState_next(x_2, x_4, x_19);
lean_dec(x_19);
lean_dec(x_4);
x_44 = l_Lean_Parser_binNumberFn(x_5, x_1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lean_Parser_ParserState_next(x_2, x_4, x_19);
lean_dec(x_19);
lean_dec(x_4);
x_46 = l_Lean_Parser_binNumberFn(x_5, x_1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_47 = lean_box(0);
x_48 = l_Lean_Parser_satisfyFn___closed__1;
x_49 = 1;
x_50 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_48, x_47, x_49);
return x_50;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isIdCont(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; uint32_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 2);
x_4 = lean_string_utf8_get(x_1, x_3);
x_5 = 46;
x_6 = lean_uint32_dec_eq(x_4, x_5);
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
uint32_t x_10; lean_object* x_11; uint32_t x_20; uint8_t x_21; 
x_10 = lean_string_utf8_get(x_1, x_8);
lean_dec(x_8);
x_20 = 65;
x_21 = lean_uint32_dec_le(x_20, x_10);
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 97;
x_23 = lean_uint32_dec_le(x_22, x_10);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_box(0);
x_11 = x_24;
goto block_19;
}
else
{
uint32_t x_25; uint8_t x_26; 
x_25 = 122;
x_26 = lean_uint32_dec_le(x_10, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_box(0);
x_11 = x_27;
goto block_19;
}
else
{
uint8_t x_28; 
x_28 = 1;
return x_28;
}
}
}
else
{
uint32_t x_29; uint8_t x_30; 
x_29 = 90;
x_30 = lean_uint32_dec_le(x_10, x_29);
if (x_30 == 0)
{
uint32_t x_31; uint8_t x_32; 
x_31 = 97;
x_32 = lean_uint32_dec_le(x_31, x_10);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_box(0);
x_11 = x_33;
goto block_19;
}
else
{
uint32_t x_34; uint8_t x_35; 
x_34 = 122;
x_35 = lean_uint32_dec_le(x_10, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_box(0);
x_11 = x_36;
goto block_19;
}
else
{
uint8_t x_37; 
x_37 = 1;
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = 1;
return x_38;
}
}
block_19:
{
uint32_t x_12; uint8_t x_13; 
lean_dec(x_11);
x_12 = 95;
x_13 = lean_uint32_dec_eq(x_10, x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_isLetterLike(x_10);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = l_Lean_idBeginEscape;
x_16 = lean_uint32_dec_eq(x_10, x_15);
return x_16;
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
else
{
uint8_t x_39; 
lean_dec(x_8);
x_39 = 0;
return x_39;
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
static lean_object* _init_l_Lean_Parser_mkTokenAndFixPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("token", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkTokenAndFixPos___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forbidden token", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_9);
x_12 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_224____spec__1(x_11, x_2);
lean_dec(x_2);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 2);
lean_dec(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_dec(x_17);
lean_inc_n(x_1, 2);
lean_inc(x_15);
lean_ctor_set(x_13, 2, x_1);
lean_ctor_set(x_13, 1, x_1);
x_18 = lean_string_utf8_byte_size(x_9);
x_19 = lean_nat_add(x_1, x_18);
lean_dec(x_18);
lean_inc(x_19);
x_20 = l_Lean_Parser_ParserState_setPos(x_4, x_19);
x_21 = l_Lean_Parser_whitespace(x_3, x_20);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
lean_inc(x_19);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_1);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_19);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_9);
x_26 = l_Lean_Parser_ParserState_pushSyntax(x_21, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
lean_dec(x_13);
lean_inc_n(x_1, 2);
lean_inc(x_27);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_1);
lean_ctor_set(x_28, 2, x_1);
x_29 = lean_string_utf8_byte_size(x_9);
x_30 = lean_nat_add(x_1, x_29);
lean_dec(x_29);
lean_inc(x_30);
x_31 = l_Lean_Parser_ParserState_setPos(x_4, x_30);
x_32 = l_Lean_Parser_whitespace(x_3, x_31);
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
lean_inc(x_30);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_1);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_30);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_9);
x_37 = l_Lean_Parser_ParserState_pushSyntax(x_32, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_9);
lean_dec(x_3);
x_38 = lean_box(0);
x_39 = l_Lean_Parser_mkTokenAndFixPos___closed__2;
x_40 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_39, x_1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
lean_dec(x_2);
x_42 = lean_ctor_get(x_3, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
lean_dec(x_42);
lean_inc(x_41);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_45 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___private_Lean_Parser_Types_0__Lean_Parser_beqCacheableParserContext____x40_Lean_Parser_Types___hyg_224____spec__1(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
lean_inc_n(x_1, 2);
lean_inc(x_47);
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 3, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_1);
lean_ctor_set(x_49, 2, x_1);
x_50 = lean_string_utf8_byte_size(x_41);
x_51 = lean_nat_add(x_1, x_50);
lean_dec(x_50);
lean_inc(x_51);
x_52 = l_Lean_Parser_ParserState_setPos(x_4, x_51);
x_53 = l_Lean_Parser_whitespace(x_3, x_52);
x_54 = lean_ctor_get(x_53, 2);
lean_inc(x_54);
lean_inc(x_51);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_55, 2, x_54);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_1);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_51);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_41);
x_58 = l_Lean_Parser_ParserState_pushSyntax(x_53, x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_41);
lean_dec(x_3);
x_59 = lean_box(0);
x_60 = l_Lean_Parser_mkTokenAndFixPos___closed__2;
x_61 = l_Lean_Parser_ParserState_mkErrorAt(x_4, x_60, x_1, x_59);
return x_61;
}
}
}
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
lean_object* x_8; uint8_t x_9; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_10);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 1, x_1);
x_13 = l_Lean_Parser_whitespace(x_4, x_5);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_inc_n(x_1, 2);
lean_inc(x_10);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_1);
lean_ctor_set(x_15, 2, x_1);
lean_inc(x_6);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_6);
lean_ctor_set(x_16, 2, x_14);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_6);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_8);
lean_ctor_set(x_19, 2, x_3);
lean_ctor_set(x_19, 3, x_18);
x_20 = l_Lean_Parser_ParserState_pushSyntax(x_13, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_21);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_1);
lean_ctor_set(x_22, 2, x_6);
x_23 = l_Lean_Parser_whitespace(x_4, x_5);
x_24 = lean_ctor_get(x_23, 2);
lean_inc(x_24);
lean_inc_n(x_1, 2);
lean_inc(x_21);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_1);
lean_ctor_set(x_25, 2, x_1);
lean_inc(x_6);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_26, 2, x_24);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_1);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_27, 3, x_6);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_3);
lean_ctor_set(x_29, 3, x_28);
x_30 = l_Lean_Parser_ParserState_pushSyntax(x_23, x_29);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_6);
lean_dec(x_3);
x_31 = l_Lean_Parser_mkTokenAndFixPos(x_1, x_2, x_4, x_5);
return x_31;
}
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
x_1 = lean_mk_string_unchecked("unterminated identifier escape", 30, 30);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_21; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_21 = lean_string_utf8_at_end(x_7, x_8);
if (x_21 == 0)
{
uint32_t x_22; lean_object* x_23; uint32_t x_31; uint8_t x_32; 
x_22 = lean_string_utf8_get_fast(x_7, x_8);
x_31 = l_Lean_idBeginEscape;
x_32 = lean_uint32_dec_eq(x_22, x_31);
if (x_32 == 0)
{
uint32_t x_33; uint8_t x_34; 
x_33 = 65;
x_34 = lean_uint32_dec_le(x_33, x_22);
if (x_34 == 0)
{
uint32_t x_35; uint8_t x_36; 
x_35 = 97;
x_36 = lean_uint32_dec_le(x_35, x_22);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_box(0);
x_23 = x_37;
goto block_30;
}
else
{
uint32_t x_38; uint8_t x_39; 
x_38 = 122;
x_39 = lean_uint32_dec_le(x_22, x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_box(0);
x_23 = x_40;
goto block_30;
}
else
{
lean_object* x_41; 
x_41 = lean_box(0);
x_9 = x_41;
goto block_20;
}
}
}
else
{
uint32_t x_42; uint8_t x_43; 
x_42 = 90;
x_43 = lean_uint32_dec_le(x_22, x_42);
if (x_43 == 0)
{
uint32_t x_44; uint8_t x_45; 
x_44 = 97;
x_45 = lean_uint32_dec_le(x_44, x_22);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_box(0);
x_23 = x_46;
goto block_30;
}
else
{
uint32_t x_47; uint8_t x_48; 
x_47 = 122;
x_48 = lean_uint32_dec_le(x_22, x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_box(0);
x_23 = x_49;
goto block_30;
}
else
{
lean_object* x_50; 
x_50 = lean_box(0);
x_9 = x_50;
goto block_20;
}
}
}
else
{
lean_object* x_51; 
x_51 = lean_box(0);
x_9 = x_51;
goto block_20;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_52 = lean_string_utf8_next_fast(x_7, x_8);
lean_dec(x_8);
lean_inc(x_52);
x_53 = l_Lean_Parser_ParserState_setPos(x_5, x_52);
x_54 = l_Lean_Parser_identFnAux_parse___closed__2;
x_55 = l_Lean_Parser_takeUntilFn(x_54, x_4, x_53);
x_56 = lean_ctor_get(x_55, 2);
lean_inc(x_56);
x_57 = lean_string_utf8_at_end(x_7, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = l_Lean_Parser_ParserState_next_x27(x_55, x_7, x_56, lean_box(0));
x_59 = lean_string_utf8_extract(x_7, x_52, x_56);
lean_dec(x_52);
x_60 = l_Lean_Name_str___override(x_3, x_59);
x_61 = l_Lean_Parser_isIdCont(x_7, x_58);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_56);
lean_dec(x_7);
x_62 = l_Lean_Parser_mkIdResult(x_1, x_2, x_60, x_4, x_58);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_string_utf8_next_fast(x_7, x_56);
lean_dec(x_56);
x_64 = l_Lean_Parser_ParserState_next(x_58, x_7, x_63);
lean_dec(x_63);
lean_dec(x_7);
x_3 = x_60;
x_5 = x_64;
goto _start;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_56);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = l_Lean_Parser_identFnAux_parse___closed__3;
x_67 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_55, x_66, x_52);
return x_67;
}
}
block_30:
{
uint32_t x_24; uint8_t x_25; 
lean_dec(x_23);
x_24 = 95;
x_25 = lean_uint32_dec_eq(x_22, x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_isLetterLike(x_22);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_27 = l_Lean_Parser_mkTokenAndFixPos(x_1, x_2, x_4, x_5);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = lean_box(0);
x_9 = x_28;
goto block_20;
}
}
else
{
lean_object* x_29; 
x_29 = lean_box(0);
x_9 = x_29;
goto block_20;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = lean_box(0);
x_69 = l_Lean_Parser_satisfyFn___closed__1;
x_70 = 1;
x_71 = l_Lean_Parser_ParserState_mkUnexpectedError(x_5, x_69, x_68, x_70);
return x_71;
}
block_20:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_9);
x_10 = l_Lean_Parser_ParserState_next(x_5, x_7, x_8);
x_11 = l_Lean_Parser_identFnAux_parse___closed__1;
x_12 = l_Lean_Parser_takeWhileFn(x_11, x_4, x_10);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
x_14 = lean_string_utf8_extract(x_7, x_8, x_13);
lean_dec(x_8);
x_15 = l_Lean_Name_str___override(x_3, x_14);
x_16 = l_Lean_Parser_isIdCont(x_7, x_12);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_7);
x_17 = l_Lean_Parser_mkIdResult(x_1, x_2, x_15, x_4, x_12);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_Parser_ParserState_next(x_12, x_7, x_13);
lean_dec(x_13);
lean_dec(x_7);
x_3 = x_15;
x_5 = x_18;
goto _start;
}
}
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
lean_object* x_2; uint32_t x_11; uint8_t x_12; 
x_11 = 65;
x_12 = lean_uint32_dec_le(x_11, x_1);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 97;
x_14 = lean_uint32_dec_le(x_13, x_1);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_box(0);
x_2 = x_15;
goto block_10;
}
else
{
uint32_t x_16; uint8_t x_17; 
x_16 = 122;
x_17 = lean_uint32_dec_le(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_box(0);
x_2 = x_18;
goto block_10;
}
else
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
}
}
else
{
uint32_t x_20; uint8_t x_21; 
x_20 = 90;
x_21 = lean_uint32_dec_le(x_1, x_20);
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 97;
x_23 = lean_uint32_dec_le(x_22, x_1);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_box(0);
x_2 = x_24;
goto block_10;
}
else
{
uint32_t x_25; uint8_t x_26; 
x_25 = 122;
x_26 = lean_uint32_dec_le(x_1, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_box(0);
x_2 = x_27;
goto block_10;
}
else
{
uint8_t x_28; 
x_28 = 1;
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = 1;
return x_29;
}
}
block_10:
{
uint32_t x_3; uint8_t x_4; 
lean_dec(x_2);
x_3 = 95;
x_4 = lean_uint32_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_isLetterLike(x_1);
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = l_Lean_idBeginEscape;
x_7 = lean_uint32_dec_eq(x_1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
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
x_1 = lean_mk_string_unchecked("invalid Name literal", 20, 20);
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
x_11 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_10, x_6);
if (x_11 == 0)
{
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = l_Lean_Parser_SyntaxStack_back(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 3)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
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
x_21 = l_Lean_Syntax_mkNameLit(x_20, x_14);
x_22 = l_Lean_Parser_ParserState_pushSyntax(x_16, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
x_23 = l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__1;
x_24 = l_Lean_Parser_ParserState_mkError(x_9, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_44; uint32_t x_53; uint8_t x_54; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_string_utf8_get(x_4, x_5);
x_53 = 34;
x_54 = lean_uint32_dec_eq(x_6, x_53);
if (x_54 == 0)
{
uint32_t x_55; uint8_t x_56; 
x_55 = 39;
x_56 = lean_uint32_dec_eq(x_6, x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_box(0);
x_44 = x_57;
goto block_52;
}
else
{
uint32_t x_58; uint8_t x_59; 
x_58 = l_Lean_Parser_getNext(x_4, x_5);
x_59 = lean_uint32_dec_eq(x_58, x_55);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_4);
x_61 = l_Lean_Parser_charLitFnAux(x_5, x_1, x_60);
return x_61;
}
else
{
lean_object* x_62; 
x_62 = lean_box(0);
x_44 = x_62;
goto block_52;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_4);
x_64 = l_Lean_Parser_strLitFnAux(x_5, x_1, x_63);
return x_64;
}
block_43:
{
uint32_t x_8; uint8_t x_9; 
lean_dec(x_7);
x_8 = 96;
x_9 = lean_uint32_dec_eq(x_6, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 114;
x_11 = lean_uint32_dec_eq(x_6, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_inc(x_5);
x_13 = l_Lean_Data_Trie_matchPrefix___rarg(x_4, x_12, x_5);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = l_Lean_Parser_identFnAux_parse(x_5, x_13, x_14, x_1, x_2);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_string_utf8_next(x_4, x_5);
x_17 = l_Lean_Parser_isRawStrLitStart(x_4, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
lean_inc(x_5);
x_19 = l_Lean_Data_Trie_matchPrefix___rarg(x_4, x_18, x_5);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = l_Lean_Parser_identFnAux_parse(x_5, x_19, x_20, x_1, x_2);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_4);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Parser_rawStrLitFnAux_initState(x_5, x_23, x_1, x_22);
return x_24;
}
}
}
else
{
uint32_t x_25; uint8_t x_26; 
x_25 = l_Lean_Parser_getNext(x_4, x_5);
x_26 = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(x_25);
if (x_26 == 0)
{
uint32_t x_27; uint8_t x_28; 
x_27 = 114;
x_28 = lean_uint32_dec_eq(x_6, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_1, 3);
lean_inc(x_29);
lean_inc(x_5);
x_30 = l_Lean_Data_Trie_matchPrefix___rarg(x_4, x_29, x_5);
lean_dec(x_4);
x_31 = lean_box(0);
x_32 = l_Lean_Parser_identFnAux_parse(x_5, x_30, x_31, x_1, x_2);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_string_utf8_next(x_4, x_5);
x_34 = l_Lean_Parser_isRawStrLitStart(x_4, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_1, 3);
lean_inc(x_35);
lean_inc(x_5);
x_36 = l_Lean_Data_Trie_matchPrefix___rarg(x_4, x_35, x_5);
lean_dec(x_4);
x_37 = lean_box(0);
x_38 = l_Lean_Parser_identFnAux_parse(x_5, x_36, x_37, x_1, x_2);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = l_Lean_Parser_ParserState_next(x_2, x_4, x_5);
lean_dec(x_4);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Lean_Parser_rawStrLitFnAux_initState(x_5, x_40, x_1, x_39);
return x_41;
}
}
}
else
{
lean_object* x_42; 
lean_dec(x_4);
x_42 = l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(x_5, x_1, x_2);
return x_42;
}
}
}
block_52:
{
uint32_t x_45; uint8_t x_46; 
lean_dec(x_44);
x_45 = 48;
x_46 = lean_uint32_dec_le(x_45, x_6);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_box(0);
x_7 = x_47;
goto block_43;
}
else
{
uint32_t x_48; uint8_t x_49; 
x_48 = 57;
x_49 = lean_uint32_dec_le(x_6, x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_box(0);
x_7 = x_50;
goto block_43;
}
else
{
lean_object* x_51; 
lean_dec(x_5);
lean_dec(x_4);
x_51 = l_Lean_Parser_numberFnAux(x_1, x_2);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 4);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 0);
lean_dec(x_11);
x_12 = l_Lean_Parser_SyntaxStack_size(x_5);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_2, 5);
lean_dec(x_16);
x_17 = lean_ctor_get(x_2, 4);
lean_dec(x_17);
x_18 = lean_ctor_get(x_2, 3);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 2);
lean_dec(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_2, 0);
lean_dec(x_21);
x_22 = l_Lean_Parser_SyntaxStack_back(x_5);
lean_inc(x_7);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_7);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_3, 0, x_23);
x_24 = lean_box(0);
lean_ctor_set(x_2, 4, x_24);
return x_2;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
x_25 = l_Lean_Parser_SyntaxStack_back(x_5);
lean_inc(x_7);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_7);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set(x_3, 0, x_26);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_6);
lean_ctor_set(x_28, 2, x_7);
lean_ctor_set(x_28, 3, x_3);
lean_ctor_set(x_28, 4, x_27);
lean_ctor_set(x_28, 5, x_8);
return x_28;
}
}
else
{
lean_free_object(x_3);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_2;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
lean_dec(x_3);
x_30 = l_Lean_Parser_SyntaxStack_size(x_5);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_33 = x_2;
} else {
 lean_dec_ref(x_2);
 x_33 = lean_box(0);
}
x_34 = l_Lean_Parser_SyntaxStack_back(x_5);
lean_inc(x_7);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_7);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
x_37 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_38 = lean_alloc_ctor(0, 6, 0);
} else {
 x_38 = x_33;
}
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_6);
lean_ctor_set(x_38, 2, x_7);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 4, x_37);
lean_ctor_set(x_38, 5, x_8);
return x_38;
}
else
{
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_2;
}
}
}
else
{
lean_dec(x_4);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_nat_dec_eq(x_10, x_6);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(x_2, x_3);
x_13 = l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(x_6, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_2);
x_14 = lean_ctor_get(x_9, 2);
lean_inc(x_14);
x_15 = l_Lean_Parser_ParserState_pushSyntax(x_3, x_14);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = l_Lean_Parser_ParserState_setPos(x_15, x_16);
return x_17;
}
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_2);
x_18 = l_Lean_Parser_satisfyFn___closed__1;
x_19 = 1;
x_20 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_18, x_1, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekTokenAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Parser_ParserState_stackSize(x_2);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = l_Lean_Parser_tokenFn(x_5, x_1, x_2);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = l_Lean_Parser_SyntaxStack_back(x_8);
lean_dec(x_8);
x_10 = l_Lean_Parser_ParserState_restore(x_6, x_3, x_4);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
lean_inc(x_6);
x_15 = l_Lean_Parser_ParserState_restore(x_6, x_3, x_4);
lean_dec(x_3);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
lean_inc(x_6);
x_17 = l_Lean_Parser_ParserState_restore(x_6, x_3, x_4);
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekToken(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = l_Lean_Parser_peekTokenAux(x_1, x_2);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = l_Lean_Parser_satisfyFn___closed__1;
x_12 = 1;
x_13 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_11, x_10, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = l_Lean_Parser_SyntaxStack_back(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 2)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_1(x_4, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(x_1, x_2, x_3);
return x_11;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
else
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_4);
x_12 = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(x_1, x_2, x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_inc(x_2);
x_6 = l_Lean_Parser_tokenFn(x_2, x_3, x_4);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Parser_satisfySymbolFn___lambda__2(x_6, x_2, x_5, x_1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_satisfySymbolFn___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_satisfySymbolFn___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_symbolFnAux___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_symbolFnAux___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_Parser_satisfySymbolFn(x_5, x_7, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_symbolFnAux___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_symbolFn(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_1, x_2, x_3);
x_5 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_1, x_4, x_2);
x_6 = lean_string_utf8_extract(x_1, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_6);
x_7 = l_Lean_Parser_symbolInfo(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_symbolNoAntiquot___elambda__1), 3, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
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
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Parser_ParserState_mkUnexpectedTokenError(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = l_Lean_Parser_SyntaxStack_back(x_5);
lean_dec(x_5);
switch (lean_obj_tag(x_6)) {
case 2:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_string_dec_eq(x_3, x_7);
lean_dec(x_7);
lean_dec(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Parser_ParserState_mkUnexpectedTokenError(x_1, x_2, x_9);
return x_10;
}
else
{
lean_dec(x_2);
return x_1;
}
}
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 2);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_string_utf8_extract(x_13, x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_17 = lean_string_dec_eq(x_3, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Parser_ParserState_mkUnexpectedTokenError(x_1, x_2, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_20 = l_Lean_Parser_ParserState_popSyntax(x_1);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_3);
x_22 = l_Lean_Parser_ParserState_pushSyntax(x_20, x_21);
return x_22;
}
}
default: 
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_6);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Parser_ParserState_mkUnexpectedTokenError(x_1, x_2, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_box(0);
lean_inc(x_2);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Parser_tokenFn(x_6, x_3, x_4);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Parser_nonReservedSymbolFnAux___lambda__2(x_7, x_2, x_1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_nonReservedSymbolFnAux___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_nonReservedSymbolFnAux___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
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
x_1 = lean_mk_string_unchecked("ident", 5, 5);
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
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_nonReservedSymbolFn(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_1, x_3, x_4);
x_6 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_1, x_5, x_3);
x_7 = lean_string_utf8_extract(x_1, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_inc(x_7);
x_8 = l_Lean_Parser_nonReservedSymbolInfo(x_7, x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolNoAntiquot___elambda__1), 3, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
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
x_11 = lean_string_utf8_get_fast(x_1, x_3);
x_12 = lean_string_utf8_get_fast(x_9, x_7);
x_13 = lean_uint32_dec_eq(x_11, x_12);
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
x_15 = lean_string_utf8_next_fast(x_1, x_3);
lean_dec(x_3);
x_16 = l_Lean_Parser_ParserState_next_x27(x_5, x_9, x_7, lean_box(0));
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
x_5 = l_Lean_Parser_SyntaxStack_back(x_4);
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
static lean_object* _init_l___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkWsBefore", 13, 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The `ws` parser requires that there is some whitespace at this location.\nFor example, the parser `\"foo\" ws \"+\"` parses `foo +` or `foo/- -/+` but not `foo+`.\n\nThis parser has arity 0 - it does not capture anything. ", 215, 215);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkWsBefore_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
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
LEAN_EXPORT uint8_t l_String_anyAux___at_Lean_Parser_checkTailLinebreak___spec__1(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
uint32_t x_7; uint8_t x_8; 
x_7 = lean_string_utf8_get(x_2, x_4);
x_8 = lean_uint32_dec_eq(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec(x_4);
x_11 = 1;
return x_11;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailLinebreak(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint32_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_dec(x_2);
x_4 = 10;
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_String_anyAux___at_Lean_Parser_checkTailLinebreak___spec__1(x_4, x_5, x_7, x_6);
lean_dec(x_7);
lean_dec(x_5);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = 0;
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at_Lean_Parser_checkTailLinebreak___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = l_String_anyAux___at_Lean_Parser_checkTailLinebreak___spec__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(x_6);
return x_7;
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
x_5 = l_Lean_Parser_SyntaxStack_back(x_4);
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
static lean_object* _init_l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkLinebreakBefore", 20, 20);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The `linebreak` parser requires that there is at least one line break at this location.\n(The line break may be inside a comment.)\n\nThis parser has arity 0 - it does not capture anything. ", 187, 187);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
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
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Subarray_get___rarg(x_1, x_7);
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Parser_SyntaxStack_toSubarray(x_1);
x_3 = l_Subarray_size___rarg(x_2);
x_4 = l_Subarray_findSomeRevM_x3f_find___at___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___spec__1(x_2, x_3, lean_box(0));
lean_dec(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_findSomeRevM_x3f_find___at___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Subarray_findSomeRevM_x3f_find___at___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(x_4);
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
static lean_object* _init_l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkNoWsBefore", 15, 15);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The `noWs` parser requires that there is *no* whitespace between the preceding and following\nparsers. For example, the parser `\"foo\" noWs \"+\"` parses `foo+` but not `foo +`.\n\nThis is almost the same as `\"foo+\"`, but using this parser will make `foo+` a token, which may cause\nproblems for the use of `\"foo\"` and `\"+\"` as separate tokens in other parsers.\n\nThis parser has arity 0 - it does not capture anything. ", 412, 412);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
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
LEAN_EXPORT uint8_t l_Lean_Parser_unicodeSymbolFnAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_dec_eq(x_3, x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_string_dec_eq(x_3, x_2);
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
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFnAux___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
x_7 = l_Lean_Parser_satisfySymbolFn(x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Parser_unicodeSymbolFnAux___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
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
x_1 = lean_mk_string_unchecked("', '", 4, 4);
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
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_unicodeSymbolFn(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_1, x_3, x_4);
x_6 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_1, x_5, x_3);
x_7 = lean_string_utf8_extract(x_1, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_string_utf8_byte_size(x_2);
x_9 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_2, x_8, x_4);
x_10 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_2, x_9, x_8);
x_11 = lean_string_utf8_extract(x_2, x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
lean_inc(x_11);
lean_inc(x_7);
x_12 = l_Lean_Parser_unicodeSymbolInfo(x_7, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolNoAntiquot___elambda__1), 4, 2);
lean_closure_set(x_13, 0, x_7);
lean_closure_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
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
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_box(0);
lean_inc(x_2);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Parser_tokenFn(x_6, x_3, x_4);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = l_Lean_Parser_SyntaxStack_back(x_11);
lean_dec(x_11);
x_13 = l_Lean_Syntax_isOfKind(x_12, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Parser_ParserState_mkUnexpectedTokenError(x_7, x_2, x_14);
return x_15;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_expectTokenFn(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Parser_decimalNumberFn___closed__3;
x_4 = l_Lean_Parser_numberFnAux___closed__1;
x_5 = l_Lean_Parser_expectTokenFn(x_3, x_4, x_1, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_decimalNumberFn___closed__2;
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
x_1 = lean_mk_string_unchecked("scientific number", 17, 17);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Parser_decimalNumberFn_parseScientific___closed__2;
x_4 = l_Lean_Parser_scientificLitFn___closed__1;
x_5 = l_Lean_Parser_expectTokenFn(x_3, x_4, x_1, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_decimalNumberFn_parseScientific___closed__1;
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
x_1 = lean_mk_string_unchecked("string literal", 14, 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Parser_strLitFnAux___closed__3;
x_4 = l_Lean_Parser_strLitFn___closed__1;
x_5 = l_Lean_Parser_expectTokenFn(x_3, x_4, x_1, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_strLitFnAux___closed__2;
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
x_1 = lean_mk_string_unchecked("character literal", 17, 17);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Parser_charLitFnAux___closed__3;
x_4 = l_Lean_Parser_charLitFn___closed__1;
x_5 = l_Lean_Parser_expectTokenFn(x_3, x_4, x_1, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_charLitFnAux___closed__2;
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
x_1 = lean_mk_string_unchecked("name", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_nameLitFn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_nameLitFn___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_nameLitFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Name literal", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Parser_nameLitFn___closed__2;
x_4 = l_Lean_Parser_nameLitFn___closed__3;
x_5 = l_Lean_Parser_expectTokenFn(x_3, x_4, x_1, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_nameLitFn___closed__1;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_nonReservedSymbolInfo___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_identFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("identifier", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Parser_identFn___closed__1;
x_4 = l_Lean_Parser_identFn___closed__2;
x_5 = l_Lean_Parser_expectTokenFn(x_3, x_4, x_1, x_2);
return x_5;
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
LEAN_EXPORT uint8_t l_Lean_Parser_identEqFn___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_identEqFn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_identFn___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_identEqFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_identEqFn___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_identEqFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("identifier '", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEqFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = l_Lean_Parser_identEqFn___closed__1;
x_5 = l_Lean_Parser_tokenFn(x_4, x_2, x_3);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = l_Lean_Parser_SyntaxStack_back(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 3)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_11, x_1);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = 1;
x_14 = l_Lean_Parser_identEqFn___closed__2;
x_15 = l_Lean_Name_toString(x_1, x_13, x_14);
x_16 = l_Lean_Parser_identEqFn___closed__3;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_Parser_chFn___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Parser_ParserState_mkUnexpectedTokenError(x_5, x_19, x_20);
return x_21;
}
else
{
lean_dec(x_1);
return x_5;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_1);
x_22 = l_Lean_Parser_identFn___closed__2;
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Parser_ParserState_mkUnexpectedTokenError(x_5, x_22, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEqFn___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_identEqFn___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEq___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_identEqFn(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identEq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_identEq___elambda__1), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_identNoAntiquot___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoFn___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoFn___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_hygieneInfoFn___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_inc_n(x_4, 2);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_4);
lean_inc(x_4);
lean_inc_n(x_5, 2);
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set(x_6, 3, x_4);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_7);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
x_11 = lean_array_mk(x_10);
x_12 = lean_box(2);
x_13 = l_Lean_Parser_hygieneInfoFn___lambda__1___closed__2;
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_11);
x_15 = l_Lean_Parser_ParserState_pushSyntax(x_1, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
lean_dec(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_dec(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = l_Lean_Parser_SyntaxStack_isEmpty(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Parser_SyntaxStack_back(x_8);
lean_dec(x_8);
x_11 = l_Lean_Syntax_getTailInfo(x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_13 = lean_ctor_get(x_11, 2);
x_14 = lean_ctor_get(x_11, 3);
lean_inc_n(x_14, 2);
lean_ctor_set(x_3, 2, x_14);
lean_ctor_set(x_3, 1, x_14);
x_15 = l_Lean_Parser_ParserState_popSyntax(x_2);
lean_inc(x_14);
lean_inc(x_3);
lean_ctor_set(x_11, 2, x_3);
x_16 = l_Lean_Syntax_setTailInfo(x_10, x_11);
x_17 = l_Lean_Parser_ParserState_pushSyntax(x_15, x_16);
lean_inc(x_14);
lean_inc(x_3);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set(x_18, 3, x_14);
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_21, 3, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_array_mk(x_22);
x_24 = lean_box(2);
x_25 = l_Lean_Parser_hygieneInfoFn___lambda__1___closed__2;
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
x_27 = l_Lean_Parser_ParserState_pushSyntax(x_17, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
x_30 = lean_ctor_get(x_11, 2);
x_31 = lean_ctor_get(x_11, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
lean_inc_n(x_31, 2);
lean_ctor_set(x_3, 2, x_31);
lean_ctor_set(x_3, 1, x_31);
x_32 = l_Lean_Parser_ParserState_popSyntax(x_2);
lean_inc(x_31);
lean_inc(x_3);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_3);
lean_ctor_set(x_33, 3, x_31);
x_34 = l_Lean_Syntax_setTailInfo(x_10, x_33);
x_35 = l_Lean_Parser_ParserState_pushSyntax(x_32, x_34);
lean_inc(x_31);
lean_inc(x_3);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_3);
lean_ctor_set(x_39, 2, x_38);
lean_ctor_set(x_39, 3, x_37);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
x_41 = lean_array_mk(x_40);
x_42 = lean_box(2);
x_43 = l_Lean_Parser_hygieneInfoFn___lambda__1___closed__2;
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_41);
x_45 = l_Lean_Parser_ParserState_pushSyntax(x_35, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_11);
lean_dec(x_10);
lean_free_object(x_3);
x_46 = lean_box(0);
x_47 = l_Lean_Parser_hygieneInfoFn___lambda__1(x_2, x_5, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_8);
lean_free_object(x_3);
x_48 = lean_box(0);
x_49 = l_Lean_Parser_hygieneInfoFn___lambda__1(x_2, x_5, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_3, 0);
lean_inc(x_50);
lean_dec(x_3);
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
x_52 = l_Lean_Parser_SyntaxStack_isEmpty(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_Lean_Parser_SyntaxStack_back(x_51);
lean_dec(x_51);
x_54 = l_Lean_Syntax_getTailInfo(x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 3);
lean_inc(x_58);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_59 = x_54;
} else {
 lean_dec_ref(x_54);
 x_59 = lean_box(0);
}
lean_inc_n(x_58, 2);
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_58);
x_61 = l_Lean_Parser_ParserState_popSyntax(x_2);
lean_inc(x_58);
lean_inc(x_60);
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(0, 4, 0);
} else {
 x_62 = x_59;
}
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_56);
lean_ctor_set(x_62, 2, x_60);
lean_ctor_set(x_62, 3, x_58);
x_63 = l_Lean_Syntax_setTailInfo(x_53, x_62);
x_64 = l_Lean_Parser_ParserState_pushSyntax(x_61, x_63);
lean_inc(x_58);
lean_inc(x_60);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_58);
lean_ctor_set(x_65, 2, x_57);
lean_ctor_set(x_65, 3, x_58);
x_66 = lean_box(0);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_60);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set(x_68, 3, x_66);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
x_70 = lean_array_mk(x_69);
x_71 = lean_box(2);
x_72 = l_Lean_Parser_hygieneInfoFn___lambda__1___closed__2;
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_70);
x_74 = l_Lean_Parser_ParserState_pushSyntax(x_64, x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_54);
lean_dec(x_53);
x_75 = lean_box(0);
x_76 = l_Lean_Parser_hygieneInfoFn___lambda__1(x_2, x_50, x_75);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_51);
x_77 = lean_box(0);
x_78 = l_Lean_Parser_hygieneInfoFn___lambda__1(x_2, x_50, x_77);
return x_78;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hygieneInfoFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_hygieneInfoFn___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_hygieneInfoFn___lambda__1___closed__2;
x_2 = l_Lean_Parser_epsilonInfo;
x_3 = l_Lean_Parser_nodeInfo(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_hygieneInfoFn), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_hygieneInfoNoAntiquot___closed__1;
x_2 = l_Lean_Parser_hygieneInfoNoAntiquot___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_hygieneInfoNoAntiquot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_hygieneInfoNoAntiquot___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepTop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Parser_SyntaxStack_back(x_1);
x_4 = l_Lean_Parser_SyntaxStack_shrink(x_1, x_2);
x_5 = l_Lean_Parser_SyntaxStack_push(x_4, x_3);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_12 = l_Lean_Parser_ParserState_keepTop(x_6, x_2);
x_13 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
lean_ctor_set(x_13, 5, x_11);
return x_13;
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 4);
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = l_Lean_Parser_SyntaxStack_shrink(x_7, x_2);
lean_ctor_set(x_1, 4, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_5);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get(x_1, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_15 = l_Lean_Parser_SyntaxStack_shrink(x_12, x_2);
x_16 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
lean_ctor_set(x_16, 2, x_3);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set(x_16, 4, x_4);
lean_ctor_set(x_16, 5, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_keepPrevError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_ParserState_keepPrevError(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
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
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 4);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_inc(x_3);
x_10 = l___private_Lean_Parser_Types_0__Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_440_(x_3, x_9);
x_11 = l_Lean_Parser_SyntaxStack_shrink(x_6, x_2);
if (x_10 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Parser_Error_merge(x_3, x_9);
lean_ctor_set(x_4, 0, x_12);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
else
{
lean_dec(x_3);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
lean_inc(x_13);
lean_inc(x_3);
x_14 = l___private_Lean_Parser_Types_0__Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_440_(x_3, x_13);
x_15 = l_Lean_Parser_SyntaxStack_shrink(x_6, x_2);
if (x_14 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Parser_Error_merge(x_3, x_13);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_1, 4, x_17);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
else
{
lean_object* x_18; 
lean_dec(x_3);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_1, 4, x_18);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
x_23 = lean_ctor_get(x_1, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_25 = x_4;
} else {
 lean_dec_ref(x_4);
 x_25 = lean_box(0);
}
lean_inc(x_24);
lean_inc(x_3);
x_26 = l___private_Lean_Parser_Types_0__Lean_Parser_beqError____x40_Lean_Parser_Types___hyg_440_(x_3, x_24);
x_27 = l_Lean_Parser_SyntaxStack_shrink(x_19, x_2);
if (x_26 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = l_Lean_Parser_Error_merge(x_3, x_24);
if (lean_is_scalar(x_25)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_25;
}
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_20);
lean_ctor_set(x_30, 2, x_21);
lean_ctor_set(x_30, 3, x_22);
lean_ctor_set(x_30, 4, x_29);
lean_ctor_set(x_30, 5, x_23);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_3);
if (lean_is_scalar(x_25)) {
 x_31 = lean_alloc_ctor(1, 1, 0);
} else {
 x_31 = x_25;
}
lean_ctor_set(x_31, 0, x_24);
x_32 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_20);
lean_ctor_set(x_32, 2, x_21);
lean_ctor_set(x_32, 3, x_22);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_23);
return x_32;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_13 = l_Lean_Parser_ParserState_keepTop(x_8, x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_10);
lean_ctor_set(x_15, 3, x_11);
lean_ctor_set(x_15, 4, x_14);
lean_ctor_set(x_15, 5, x_12);
return x_15;
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
x_1 = lean_mk_string_unchecked("longestMatch parsers must generate exactly one Syntax node", 58, 58);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_apply_2(x_1, x_2, x_4);
x_7 = l_Lean_Parser_ParserState_stackSize(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
x_10 = lean_nat_dec_eq(x_7, x_9);
lean_dec(x_9);
lean_dec(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_6, 4);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Parser_ParserState_shrinkStack(x_6, x_3);
x_15 = lean_box(0);
x_16 = l_Lean_Parser_ParserState_pushSyntax(x_14, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Parser_invalidLongestMatchParser___closed__1;
x_18 = l_Lean_Parser_ParserState_mkError(x_6, x_17);
return x_18;
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
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 1);
lean_dec(x_7);
x_8 = l_Lean_Parser_maxPrec;
lean_ctor_set(x_5, 1, x_8);
x_9 = l_Lean_Parser_ParserState_stackSize(x_5);
x_10 = lean_box(0);
x_11 = l_Lean_Parser_runLongestMatchParser___lambda__1(x_3, x_4, x_9, x_5, x_10);
lean_dec(x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
x_16 = lean_ctor_get(x_5, 5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_17 = l_Lean_Parser_maxPrec;
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set(x_18, 3, x_14);
lean_ctor_set(x_18, 4, x_15);
lean_ctor_set(x_18, 5, x_16);
x_19 = l_Lean_Parser_ParserState_stackSize(x_18);
x_20 = lean_box(0);
x_21 = l_Lean_Parser_runLongestMatchParser___lambda__1(x_3, x_4, x_19, x_18, x_20);
lean_dec(x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_5, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
lean_ctor_set(x_5, 1, x_2);
x_25 = l_Lean_Parser_ParserState_stackSize(x_5);
x_26 = l_Lean_Parser_ParserState_pushSyntax(x_5, x_24);
x_27 = lean_box(0);
x_28 = l_Lean_Parser_runLongestMatchParser___lambda__1(x_3, x_4, x_25, x_26, x_27);
lean_dec(x_25);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
x_33 = lean_ctor_get(x_5, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_2);
lean_ctor_set(x_35, 2, x_30);
lean_ctor_set(x_35, 3, x_31);
lean_ctor_set(x_35, 4, x_32);
lean_ctor_set(x_35, 5, x_33);
x_36 = l_Lean_Parser_ParserState_stackSize(x_35);
x_37 = l_Lean_Parser_ParserState_pushSyntax(x_35, x_34);
x_38 = lean_box(0);
x_39 = l_Lean_Parser_runLongestMatchParser___lambda__1(x_3, x_4, x_36, x_37, x_38);
lean_dec(x_36);
return x_39;
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
static lean_object* _init_l_Lean_Parser_longestMatchStep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instOrdNat___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_longestMatchStep___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_longestMatchStep___closed__1;
x_2 = l_lexOrd___rarg(x_1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 4);
lean_inc(x_12);
x_13 = l_Lean_Parser_ParserState_stackSize(x_9);
x_14 = l_Lean_Parser_ParserState_restore(x_9, x_13, x_4);
x_15 = l_Lean_Parser_runLongestMatchParser(x_1, x_3, x_7, x_8, x_14);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 4);
lean_inc(x_17);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_63; 
x_63 = lean_unsigned_to_nat(1u);
x_18 = x_63;
goto block_62;
}
else
{
lean_object* x_64; 
x_64 = lean_unsigned_to_nat(0u);
x_18 = x_64;
goto block_62;
}
block_62:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
lean_inc(x_11);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_19);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_60; 
x_60 = lean_unsigned_to_nat(1u);
x_21 = x_60;
goto block_59;
}
else
{
lean_object* x_61; 
x_61 = lean_unsigned_to_nat(0u);
x_21 = x_61;
goto block_59;
}
block_59:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_inc(x_6);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
lean_inc(x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Parser_longestMatchStep___closed__1;
x_25 = l_Lean_Parser_longestMatchStep___closed__2;
x_26 = l_lexOrd___rarg(x_24, x_25);
x_27 = lean_apply_2(x_26, x_20, x_23);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
switch (x_28) {
case 0:
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
x_29 = l_Lean_Parser_ParserState_keepNewError(x_15, x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_6);
return x_30;
}
case 1:
{
lean_dec(x_11);
lean_dec(x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_13);
x_31 = lean_ctor_get(x_15, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
x_33 = lean_nat_dec_le(x_32, x_10);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_32);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 4);
lean_dec(x_35);
x_36 = lean_ctor_get(x_15, 2);
lean_dec(x_36);
x_37 = lean_ctor_get(x_15, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_15, 0);
lean_dec(x_38);
lean_ctor_set(x_15, 1, x_10);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_15);
lean_ctor_set(x_39, 1, x_6);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_15, 3);
x_41 = lean_ctor_get(x_15, 5);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_15);
x_42 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_10);
lean_ctor_set(x_42, 2, x_16);
lean_ctor_set(x_42, 3, x_40);
lean_ctor_set(x_42, 4, x_17);
lean_ctor_set(x_42, 5, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_6);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_10);
x_44 = !lean_is_exclusive(x_15);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_15, 4);
lean_dec(x_45);
x_46 = lean_ctor_get(x_15, 2);
lean_dec(x_46);
x_47 = lean_ctor_get(x_15, 1);
lean_dec(x_47);
x_48 = lean_ctor_get(x_15, 0);
lean_dec(x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_15);
lean_ctor_set(x_49, 1, x_6);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_15, 3);
x_51 = lean_ctor_get(x_15, 5);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_15);
x_52 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_52, 0, x_31);
lean_ctor_set(x_52, 1, x_32);
lean_ctor_set(x_52, 2, x_16);
lean_ctor_set(x_52, 3, x_50);
lean_ctor_set(x_52, 4, x_17);
lean_ctor_set(x_52, 5, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_6);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
x_54 = lean_ctor_get(x_12, 0);
lean_inc(x_54);
lean_dec(x_12);
x_55 = l_Lean_Parser_ParserState_mergeErrors(x_15, x_13, x_54);
lean_dec(x_13);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_6);
return x_56;
}
}
default: 
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_6);
x_57 = l_Lean_Parser_ParserState_keepPrevError(x_15, x_13, x_11, x_12, x_10);
lean_dec(x_13);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_5);
return x_58;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_1, x_3);
x_5 = l_Lean_Parser_ParserState_stackSize(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
if (x_6 == 0)
{
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Parser_orelseFnCore___lambda__1___closed__2;
x_8 = l_Lean_Parser_ParserState_mkNode(x_2, x_7, x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_longestMatchMkResult(x_1, x_2);
lean_dec(x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux_parse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_longestMatchFnAux_parse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
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
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Parser_longestMatchFnAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_Parser_longestMatchFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("longestMatch: empty list", 24, 24);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Parser_ParserState_stackSize(x_4);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_3);
lean_inc(x_15);
lean_inc(x_1);
x_19 = l_Lean_Parser_runLongestMatchParser(x_1, x_15, x_18, x_3, x_4);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = l_Lean_Parser_longestMatchFnAux_parse(x_1, x_14, x_15, x_16, x_20, x_7, x_3, x_19);
lean_dec(x_14);
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_Parser_anyOfFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("anyOf: empty list", 17, 17);
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
x_13 = 2;
x_14 = l_Lean_Parser_orelseFnCore(x_11, x_12, x_13, x_2, x_3);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEqFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_8);
x_9 = l_Lean_FileMap_toPosition(x_8, x_6);
lean_dec(x_6);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = l_Lean_FileMap_toPosition(x_8, x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_15;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkColEq", 10, 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The `colEq` parser ensures that the next token starts at exactly the column of the saved\nposition (see `withPosition`). This can be used to do whitespace sensitive syntax like\na `by` block or `do` block, where all the lines have to line up.\n\nThis parser has arity 0 - it does not capture anything. ", 298, 298);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkColEq_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEq___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkColEqFn(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkColEq___elambda__1), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_errorAtSavedPos___closed__2;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_8);
x_9 = l_Lean_FileMap_toPosition(x_8, x_6);
lean_dec(x_6);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = l_Lean_FileMap_toPosition(x_8, x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_nat_dec_le(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_15;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkColGe", 10, 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The `colGe` parser requires that the next token starts from at least the column of the saved\nposition (see `withPosition`), but allows it to be more indented.\nThis can be used for whitespace sensitive syntax to ensure that a block does not go outside a\ncertain indentation scope. For example it is used in the lean grammar for `else if`, to ensure\nthat the `else` is not less indented than the `if` it matches with.\n\nThis parser has arity 0 - it does not capture anything. ", 473, 473);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkColGe_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkColGeFn(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkColGe___elambda__1), 3, 1);
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
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_8);
x_9 = l_Lean_FileMap_toPosition(x_8, x_6);
lean_dec(x_6);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = l_Lean_FileMap_toPosition(x_8, x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_15;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkColGt", 10, 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The `colGt` parser requires that the next token starts a strictly greater column than the saved\nposition (see `withPosition`). This can be used for whitespace sensitive syntax for the arguments\nto a tactic, to ensure that the following tactic is not interpreted as an argument.\n```\nexample (x : False) : False := by\n  revert x\n  exact id\n```\nHere, the `revert` tactic is followed by a list of `colGt ident`, because otherwise it would\ninterpret `exact` as an identifier and try to revert a variable named `exact`.\n\nThis parser has arity 0 - it does not capture anything. ", 571, 571);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkColGt_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkColGtFn(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkColGt___elambda__1), 3, 1);
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
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_8);
x_9 = l_Lean_FileMap_toPosition(x_8, x_6);
lean_dec(x_6);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = l_Lean_FileMap_toPosition(x_8, x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Parser_ParserState_mkError(x_3, x_1);
return x_15;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkLineEq", 11, 11);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The `lineEq` parser requires that the current token is on the same line as the saved position\n(see `withPosition`). This can be used to ensure that composite tokens are not \"broken up\" across\ndifferent lines. For example, `else if` is parsed using `lineEq` to ensure that the two tokens\nare on the same line.\n\nThis parser has arity 0 - it does not capture anything. ", 366, 366);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkLineEq_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_checkLineEqFn(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_checkLineEq___elambda__1), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_errorAtSavedPos___closed__2;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withPosition", 12, 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_withPosition_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`withPosition(p)` runs `p` while setting the \"saved position\" to the current position.\nThis has no effect on its own, but various other parsers access this position to achieve some\ncomposite effect:\n\n* `colGt`, `colGe`, `colEq` compare the column of the saved position to the current position,\n  used to implement Python-style indentation sensitive blocks\n* `lineEq` ensures that the current position is still on the same line as the saved position,\n  used to implement composite tokens\n\nThe saved position is only available in the read-only state, which is why this is a scoping parser:\nafter the `withPosition(..)` block the saved position will be restored to its original value.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`. ", 760, 760);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withPosition_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_withPosition_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 2);
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_2, 2, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*4, x_9);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_3);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___elambda__1___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_Parser_adaptCacheableContextFn(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___elambda__1), 3, 1);
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
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___elambda__1), 3, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_withPosition___elambda__1___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Parser_checkTailLinebreak(x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 2);
lean_dec(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_3, 2, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*4, x_11);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_Lean_Parser_SyntaxStack_back(x_4);
lean_dec(x_4);
lean_inc(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___elambda__1___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_3);
x_7 = l_Lean_Parser_adaptCacheableContextFn(x_6, x_1, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___elambda__1), 3, 1);
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
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___elambda__1), 3, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_withPositionAfterLinebreak___elambda__1___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withoutPosition", 15, 15);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`withoutPosition(p)` runs `p` without the saved position, meaning that position-checking\nparsers like `colGt` will have no effect. This is usually used by bracketing constructs like\n`(...)` so that the user can locally override whitespace sensitivity.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`. ", 330, 330);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withoutPosition_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_dec(x_3);
x_4 = lean_box(0);
lean_ctor_set(x_1, 2, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_7);
return x_10;
}
}
}
static lean_object* _init_l_Lean_Parser_withoutPosition___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_withoutPosition___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_withoutPosition___closed__1;
x_3 = l_Lean_Parser_adaptCacheableContext(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withForbidden", 13, 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`withForbidden tk p` runs `p` with `tk` as a \"forbidden token\". This means that if the token\nappears anywhere in `p` (unless it is nested in `withoutForbidden`), parsing will immediately\nstop there, making `tk` effectively a lowest-precedence operator. This is used for parsers like\n`for x in arr do ...`: `arr` is parsed as `withForbidden \"do\" term` because otherwise `arr do ...`\nwould be treated as an application.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`. ", 496, 496);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withForbidden_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 3);
lean_dec(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_2, 3, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*4, x_8);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_withForbidden___lambda__1), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Parser_adaptCacheableContext(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withoutForbidden", 16, 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`withoutForbidden(p)` runs `p` disabling the \"forbidden token\" (see `withForbidden`), if any.\nThis is usually used by bracketing constructs like `(...)` because there is no parsing ambiguity\ninside these nested constructs.\n\nThis parser has the same arity as `p` - it just forwards the results of `p`. ", 301, 301);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withoutForbidden_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_dec(x_3);
x_4 = lean_box(0);
lean_ctor_set(x_1, 3, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_7);
return x_10;
}
}
}
static lean_object* _init_l_Lean_Parser_withoutForbidden___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_withoutForbidden___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_withoutForbidden___closed__1;
x_3 = l_Lean_Parser_adaptCacheableContext(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_eoiFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected end of file", 20, 20);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_14 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_9, x_2, x_3);
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
x_17 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_12, x_2, x_3);
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
x_24 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_19, x_2, x_3);
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
x_29 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_22, x_2, x_3);
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
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_33, x_2, x_3);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*4);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_38, 3);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_38, 3);
lean_dec(x_43);
x_44 = lean_ctor_get(x_38, 0);
lean_dec(x_44);
lean_ctor_set(x_38, 0, x_41);
x_45 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_38, 1);
x_47 = lean_ctor_get(x_38, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_39);
x_49 = 1;
lean_ctor_set(x_1, 0, x_48);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_41, sizeof(void*)*4);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_38, 1);
x_53 = lean_ctor_get(x_38, 2);
x_54 = lean_ctor_get(x_38, 3);
lean_dec(x_54);
x_55 = lean_ctor_get(x_38, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_41);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_41, 0);
x_58 = lean_ctor_get(x_41, 1);
x_59 = lean_ctor_get(x_41, 2);
x_60 = lean_ctor_get(x_41, 3);
x_61 = 1;
lean_ctor_set(x_41, 3, x_57);
lean_ctor_set(x_41, 2, x_53);
lean_ctor_set(x_41, 1, x_52);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_61);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_60);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_61);
x_62 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_59);
lean_ctor_set(x_1, 1, x_58);
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_62);
return x_1;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; uint8_t x_69; 
x_63 = lean_ctor_get(x_41, 0);
x_64 = lean_ctor_get(x_41, 1);
x_65 = lean_ctor_get(x_41, 2);
x_66 = lean_ctor_get(x_41, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_41);
x_67 = 1;
x_68 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_68, 0, x_40);
lean_ctor_set(x_68, 1, x_52);
lean_ctor_set(x_68, 2, x_53);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set_uint8(x_68, sizeof(void*)*4, x_67);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_66);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_67);
x_69 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_65);
lean_ctor_set(x_1, 1, x_64);
lean_ctor_set(x_1, 0, x_68);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_70 = lean_ctor_get(x_38, 1);
x_71 = lean_ctor_get(x_38, 2);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_38);
x_72 = lean_ctor_get(x_41, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_41, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_41, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_41, 3);
lean_inc(x_75);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_76 = x_41;
} else {
 lean_dec_ref(x_41);
 x_76 = lean_box(0);
}
x_77 = 1;
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(1, 4, 1);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_40);
lean_ctor_set(x_78, 1, x_70);
lean_ctor_set(x_78, 2, x_71);
lean_ctor_set(x_78, 3, x_72);
lean_ctor_set_uint8(x_78, sizeof(void*)*4, x_77);
x_79 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_34);
lean_ctor_set(x_79, 2, x_35);
lean_ctor_set(x_79, 3, x_36);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_77);
x_80 = 0;
lean_ctor_set(x_1, 3, x_79);
lean_ctor_set(x_1, 2, x_74);
lean_ctor_set(x_1, 1, x_73);
lean_ctor_set(x_1, 0, x_78);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_80);
return x_1;
}
}
else
{
uint8_t x_81; 
lean_free_object(x_1);
x_81 = !lean_is_exclusive(x_41);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_41, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_41, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_41, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_41, 0);
lean_dec(x_85);
x_86 = 1;
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_86);
return x_41;
}
else
{
uint8_t x_87; lean_object* x_88; 
lean_dec(x_41);
x_87 = 1;
x_88 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_88, 0, x_38);
lean_ctor_set(x_88, 1, x_34);
lean_ctor_set(x_88, 2, x_35);
lean_ctor_set(x_88, 3, x_36);
lean_ctor_set_uint8(x_88, sizeof(void*)*4, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
x_89 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_38);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_91 = lean_ctor_get(x_38, 1);
x_92 = lean_ctor_get(x_38, 2);
x_93 = lean_ctor_get(x_38, 3);
x_94 = lean_ctor_get(x_38, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_40);
if (x_95 == 0)
{
uint8_t x_96; uint8_t x_97; 
x_96 = 1;
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_96);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_93);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_96);
x_97 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_92);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_40);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_97);
return x_1;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; uint8_t x_104; 
x_98 = lean_ctor_get(x_40, 0);
x_99 = lean_ctor_get(x_40, 1);
x_100 = lean_ctor_get(x_40, 2);
x_101 = lean_ctor_get(x_40, 3);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_40);
x_102 = 1;
x_103 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_99);
lean_ctor_set(x_103, 2, x_100);
lean_ctor_set(x_103, 3, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*4, x_102);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_93);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_102);
x_104 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_92);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_103);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_104);
return x_1;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_105 = lean_ctor_get(x_38, 1);
x_106 = lean_ctor_get(x_38, 2);
x_107 = lean_ctor_get(x_38, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_38);
x_108 = lean_ctor_get(x_40, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_40, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_40, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_40, 3);
lean_inc(x_111);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_112 = x_40;
} else {
 lean_dec_ref(x_40);
 x_112 = lean_box(0);
}
x_113 = 1;
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(1, 4, 1);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_109);
lean_ctor_set(x_114, 2, x_110);
lean_ctor_set(x_114, 3, x_111);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_113);
x_115 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_34);
lean_ctor_set(x_115, 2, x_35);
lean_ctor_set(x_115, 3, x_36);
lean_ctor_set_uint8(x_115, sizeof(void*)*4, x_113);
x_116 = 0;
lean_ctor_set(x_1, 3, x_115);
lean_ctor_set(x_1, 2, x_106);
lean_ctor_set(x_1, 1, x_105);
lean_ctor_set(x_1, 0, x_114);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_116);
return x_1;
}
}
else
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_38, 3);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
lean_free_object(x_1);
x_118 = !lean_is_exclusive(x_40);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_119 = lean_ctor_get(x_40, 3);
lean_dec(x_119);
x_120 = lean_ctor_get(x_40, 2);
lean_dec(x_120);
x_121 = lean_ctor_get(x_40, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_40, 0);
lean_dec(x_122);
x_123 = 1;
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_123);
return x_40;
}
else
{
uint8_t x_124; lean_object* x_125; 
lean_dec(x_40);
x_124 = 1;
x_125 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_125, 0, x_38);
lean_ctor_set(x_125, 1, x_34);
lean_ctor_set(x_125, 2, x_35);
lean_ctor_set(x_125, 3, x_36);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_124);
return x_125;
}
}
else
{
uint8_t x_126; 
x_126 = lean_ctor_get_uint8(x_117, sizeof(void*)*4);
if (x_126 == 0)
{
uint8_t x_127; 
lean_free_object(x_1);
x_127 = !lean_is_exclusive(x_38);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_38, 1);
x_129 = lean_ctor_get(x_38, 2);
x_130 = lean_ctor_get(x_38, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_38, 0);
lean_dec(x_131);
x_132 = !lean_is_exclusive(x_117);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; 
x_133 = lean_ctor_get(x_117, 0);
x_134 = lean_ctor_get(x_117, 1);
x_135 = lean_ctor_get(x_117, 2);
x_136 = lean_ctor_get(x_117, 3);
x_137 = 1;
lean_inc(x_40);
lean_ctor_set(x_117, 3, x_133);
lean_ctor_set(x_117, 2, x_129);
lean_ctor_set(x_117, 1, x_128);
lean_ctor_set(x_117, 0, x_40);
x_138 = !lean_is_exclusive(x_40);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_139 = lean_ctor_get(x_40, 3);
lean_dec(x_139);
x_140 = lean_ctor_get(x_40, 2);
lean_dec(x_140);
x_141 = lean_ctor_get(x_40, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_40, 0);
lean_dec(x_142);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_137);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 0, x_136);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_137);
x_143 = 0;
lean_ctor_set(x_38, 3, x_40);
lean_ctor_set(x_38, 2, x_135);
lean_ctor_set(x_38, 1, x_134);
lean_ctor_set(x_38, 0, x_117);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_143);
return x_38;
}
else
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_40);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_137);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_136);
lean_ctor_set(x_144, 1, x_34);
lean_ctor_set(x_144, 2, x_35);
lean_ctor_set(x_144, 3, x_36);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_137);
x_145 = 0;
lean_ctor_set(x_38, 3, x_144);
lean_ctor_set(x_38, 2, x_135);
lean_ctor_set(x_38, 1, x_134);
lean_ctor_set(x_38, 0, x_117);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_145);
return x_38;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_146 = lean_ctor_get(x_117, 0);
x_147 = lean_ctor_get(x_117, 1);
x_148 = lean_ctor_get(x_117, 2);
x_149 = lean_ctor_get(x_117, 3);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_117);
x_150 = 1;
lean_inc(x_40);
x_151 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_151, 0, x_40);
lean_ctor_set(x_151, 1, x_128);
lean_ctor_set(x_151, 2, x_129);
lean_ctor_set(x_151, 3, x_146);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_152 = x_40;
} else {
 lean_dec_ref(x_40);
 x_152 = lean_box(0);
}
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_150);
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 4, 1);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_34);
lean_ctor_set(x_153, 2, x_35);
lean_ctor_set(x_153, 3, x_36);
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_150);
x_154 = 0;
lean_ctor_set(x_38, 3, x_153);
lean_ctor_set(x_38, 2, x_148);
lean_ctor_set(x_38, 1, x_147);
lean_ctor_set(x_38, 0, x_151);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_154);
return x_38;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; 
x_155 = lean_ctor_get(x_38, 1);
x_156 = lean_ctor_get(x_38, 2);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_38);
x_157 = lean_ctor_get(x_117, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_117, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_117, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_117, 3);
lean_inc(x_160);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 x_161 = x_117;
} else {
 lean_dec_ref(x_117);
 x_161 = lean_box(0);
}
x_162 = 1;
lean_inc(x_40);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(1, 4, 1);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_40);
lean_ctor_set(x_163, 1, x_155);
lean_ctor_set(x_163, 2, x_156);
lean_ctor_set(x_163, 3, x_157);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_164 = x_40;
} else {
 lean_dec_ref(x_40);
 x_164 = lean_box(0);
}
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_162);
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 4, 1);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_160);
lean_ctor_set(x_165, 1, x_34);
lean_ctor_set(x_165, 2, x_35);
lean_ctor_set(x_165, 3, x_36);
lean_ctor_set_uint8(x_165, sizeof(void*)*4, x_162);
x_166 = 0;
x_167 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_167, 0, x_163);
lean_ctor_set(x_167, 1, x_158);
lean_ctor_set(x_167, 2, x_159);
lean_ctor_set(x_167, 3, x_165);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_166);
return x_167;
}
}
else
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_38);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_ctor_get(x_38, 3);
lean_dec(x_169);
x_170 = lean_ctor_get(x_38, 0);
lean_dec(x_170);
x_171 = !lean_is_exclusive(x_40);
if (x_171 == 0)
{
uint8_t x_172; 
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_126);
x_172 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_172);
return x_1;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_173 = lean_ctor_get(x_40, 0);
x_174 = lean_ctor_get(x_40, 1);
x_175 = lean_ctor_get(x_40, 2);
x_176 = lean_ctor_get(x_40, 3);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_40);
x_177 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_174);
lean_ctor_set(x_177, 2, x_175);
lean_ctor_set(x_177, 3, x_176);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_126);
lean_ctor_set(x_38, 0, x_177);
x_178 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_178);
return x_1;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_179 = lean_ctor_get(x_38, 1);
x_180 = lean_ctor_get(x_38, 2);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_38);
x_181 = lean_ctor_get(x_40, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_40, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_40, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_40, 3);
lean_inc(x_184);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_185 = x_40;
} else {
 lean_dec_ref(x_40);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 4, 1);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_181);
lean_ctor_set(x_186, 1, x_182);
lean_ctor_set(x_186, 2, x_183);
lean_ctor_set(x_186, 3, x_184);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_126);
x_187 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_179);
lean_ctor_set(x_187, 2, x_180);
lean_ctor_set(x_187, 3, x_117);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_39);
x_188 = 1;
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_189; 
x_189 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
case 1:
{
uint8_t x_190; 
lean_dec(x_35);
lean_dec(x_34);
x_190 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_190);
return x_1;
}
default: 
{
lean_object* x_191; uint8_t x_192; 
x_191 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_36, x_2, x_3);
x_192 = lean_ctor_get_uint8(x_191, sizeof(void*)*4);
if (x_192 == 0)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_191, 3);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_191);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_196 = lean_ctor_get(x_191, 3);
lean_dec(x_196);
x_197 = lean_ctor_get(x_191, 0);
lean_dec(x_197);
lean_ctor_set(x_191, 0, x_194);
x_198 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_198);
return x_1;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_199 = lean_ctor_get(x_191, 1);
x_200 = lean_ctor_get(x_191, 2);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_191);
x_201 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_201, 0, x_194);
lean_ctor_set(x_201, 1, x_199);
lean_ctor_set(x_201, 2, x_200);
lean_ctor_set(x_201, 3, x_194);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_192);
x_202 = 1;
lean_ctor_set(x_1, 3, x_201);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
}
}
else
{
uint8_t x_203; 
x_203 = lean_ctor_get_uint8(x_194, sizeof(void*)*4);
if (x_203 == 0)
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_191);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_191, 1);
x_206 = lean_ctor_get(x_191, 2);
x_207 = lean_ctor_get(x_191, 3);
lean_dec(x_207);
x_208 = lean_ctor_get(x_191, 0);
lean_dec(x_208);
x_209 = !lean_is_exclusive(x_194);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; 
x_210 = lean_ctor_get(x_194, 0);
x_211 = lean_ctor_get(x_194, 1);
x_212 = lean_ctor_get(x_194, 2);
x_213 = lean_ctor_get(x_194, 3);
x_214 = 1;
lean_ctor_set(x_194, 3, x_193);
lean_ctor_set(x_194, 2, x_35);
lean_ctor_set(x_194, 1, x_34);
lean_ctor_set(x_194, 0, x_33);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_214);
lean_ctor_set(x_191, 3, x_213);
lean_ctor_set(x_191, 2, x_212);
lean_ctor_set(x_191, 1, x_211);
lean_ctor_set(x_191, 0, x_210);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_214);
x_215 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_215);
return x_1;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; uint8_t x_222; 
x_216 = lean_ctor_get(x_194, 0);
x_217 = lean_ctor_get(x_194, 1);
x_218 = lean_ctor_get(x_194, 2);
x_219 = lean_ctor_get(x_194, 3);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_194);
x_220 = 1;
x_221 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_221, 0, x_33);
lean_ctor_set(x_221, 1, x_34);
lean_ctor_set(x_221, 2, x_35);
lean_ctor_set(x_221, 3, x_193);
lean_ctor_set_uint8(x_221, sizeof(void*)*4, x_220);
lean_ctor_set(x_191, 3, x_219);
lean_ctor_set(x_191, 2, x_218);
lean_ctor_set(x_191, 1, x_217);
lean_ctor_set(x_191, 0, x_216);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_220);
x_222 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_221);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_222);
return x_1;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_223 = lean_ctor_get(x_191, 1);
x_224 = lean_ctor_get(x_191, 2);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_191);
x_225 = lean_ctor_get(x_194, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_194, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_194, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_194, 3);
lean_inc(x_228);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_229 = x_194;
} else {
 lean_dec_ref(x_194);
 x_229 = lean_box(0);
}
x_230 = 1;
if (lean_is_scalar(x_229)) {
 x_231 = lean_alloc_ctor(1, 4, 1);
} else {
 x_231 = x_229;
}
lean_ctor_set(x_231, 0, x_33);
lean_ctor_set(x_231, 1, x_34);
lean_ctor_set(x_231, 2, x_35);
lean_ctor_set(x_231, 3, x_193);
lean_ctor_set_uint8(x_231, sizeof(void*)*4, x_230);
x_232 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_232, 0, x_225);
lean_ctor_set(x_232, 1, x_226);
lean_ctor_set(x_232, 2, x_227);
lean_ctor_set(x_232, 3, x_228);
lean_ctor_set_uint8(x_232, sizeof(void*)*4, x_230);
x_233 = 0;
lean_ctor_set(x_1, 3, x_232);
lean_ctor_set(x_1, 2, x_224);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_1, 0, x_231);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
}
else
{
uint8_t x_234; 
lean_free_object(x_1);
x_234 = !lean_is_exclusive(x_194);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_235 = lean_ctor_get(x_194, 3);
lean_dec(x_235);
x_236 = lean_ctor_get(x_194, 2);
lean_dec(x_236);
x_237 = lean_ctor_get(x_194, 1);
lean_dec(x_237);
x_238 = lean_ctor_get(x_194, 0);
lean_dec(x_238);
x_239 = 1;
lean_ctor_set(x_194, 3, x_191);
lean_ctor_set(x_194, 2, x_35);
lean_ctor_set(x_194, 1, x_34);
lean_ctor_set(x_194, 0, x_33);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_239);
return x_194;
}
else
{
uint8_t x_240; lean_object* x_241; 
lean_dec(x_194);
x_240 = 1;
x_241 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_241, 0, x_33);
lean_ctor_set(x_241, 1, x_34);
lean_ctor_set(x_241, 2, x_35);
lean_ctor_set(x_241, 3, x_191);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_240);
return x_241;
}
}
}
}
else
{
uint8_t x_242; 
x_242 = lean_ctor_get_uint8(x_193, sizeof(void*)*4);
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = !lean_is_exclusive(x_191);
if (x_243 == 0)
{
lean_object* x_244; uint8_t x_245; 
x_244 = lean_ctor_get(x_191, 0);
lean_dec(x_244);
x_245 = !lean_is_exclusive(x_193);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_251; 
x_246 = lean_ctor_get(x_193, 0);
x_247 = lean_ctor_get(x_193, 1);
x_248 = lean_ctor_get(x_193, 2);
x_249 = lean_ctor_get(x_193, 3);
x_250 = 1;
lean_ctor_set(x_193, 3, x_246);
lean_ctor_set(x_193, 2, x_35);
lean_ctor_set(x_193, 1, x_34);
lean_ctor_set(x_193, 0, x_33);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_250);
lean_ctor_set(x_191, 0, x_249);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_250);
x_251 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_248);
lean_ctor_set(x_1, 1, x_247);
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_251);
return x_1;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; uint8_t x_258; 
x_252 = lean_ctor_get(x_193, 0);
x_253 = lean_ctor_get(x_193, 1);
x_254 = lean_ctor_get(x_193, 2);
x_255 = lean_ctor_get(x_193, 3);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_193);
x_256 = 1;
x_257 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_257, 0, x_33);
lean_ctor_set(x_257, 1, x_34);
lean_ctor_set(x_257, 2, x_35);
lean_ctor_set(x_257, 3, x_252);
lean_ctor_set_uint8(x_257, sizeof(void*)*4, x_256);
lean_ctor_set(x_191, 0, x_255);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_256);
x_258 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_254);
lean_ctor_set(x_1, 1, x_253);
lean_ctor_set(x_1, 0, x_257);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_258);
return x_1;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_259 = lean_ctor_get(x_191, 1);
x_260 = lean_ctor_get(x_191, 2);
x_261 = lean_ctor_get(x_191, 3);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_191);
x_262 = lean_ctor_get(x_193, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_193, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_193, 2);
lean_inc(x_264);
x_265 = lean_ctor_get(x_193, 3);
lean_inc(x_265);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_266 = x_193;
} else {
 lean_dec_ref(x_193);
 x_266 = lean_box(0);
}
x_267 = 1;
if (lean_is_scalar(x_266)) {
 x_268 = lean_alloc_ctor(1, 4, 1);
} else {
 x_268 = x_266;
}
lean_ctor_set(x_268, 0, x_33);
lean_ctor_set(x_268, 1, x_34);
lean_ctor_set(x_268, 2, x_35);
lean_ctor_set(x_268, 3, x_262);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_267);
x_269 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_269, 0, x_265);
lean_ctor_set(x_269, 1, x_259);
lean_ctor_set(x_269, 2, x_260);
lean_ctor_set(x_269, 3, x_261);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_267);
x_270 = 0;
lean_ctor_set(x_1, 3, x_269);
lean_ctor_set(x_1, 2, x_264);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_268);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
return x_1;
}
}
else
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_191, 3);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
lean_free_object(x_1);
x_272 = !lean_is_exclusive(x_193);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_273 = lean_ctor_get(x_193, 3);
lean_dec(x_273);
x_274 = lean_ctor_get(x_193, 2);
lean_dec(x_274);
x_275 = lean_ctor_get(x_193, 1);
lean_dec(x_275);
x_276 = lean_ctor_get(x_193, 0);
lean_dec(x_276);
x_277 = 1;
lean_ctor_set(x_193, 3, x_191);
lean_ctor_set(x_193, 2, x_35);
lean_ctor_set(x_193, 1, x_34);
lean_ctor_set(x_193, 0, x_33);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_277);
return x_193;
}
else
{
uint8_t x_278; lean_object* x_279; 
lean_dec(x_193);
x_278 = 1;
x_279 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_279, 0, x_33);
lean_ctor_set(x_279, 1, x_34);
lean_ctor_set(x_279, 2, x_35);
lean_ctor_set(x_279, 3, x_191);
lean_ctor_set_uint8(x_279, sizeof(void*)*4, x_278);
return x_279;
}
}
else
{
uint8_t x_280; 
x_280 = lean_ctor_get_uint8(x_271, sizeof(void*)*4);
if (x_280 == 0)
{
uint8_t x_281; 
lean_free_object(x_1);
x_281 = !lean_is_exclusive(x_191);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_282 = lean_ctor_get(x_191, 3);
lean_dec(x_282);
x_283 = lean_ctor_get(x_191, 0);
lean_dec(x_283);
x_284 = !lean_is_exclusive(x_271);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_290; 
x_285 = lean_ctor_get(x_271, 0);
x_286 = lean_ctor_get(x_271, 1);
x_287 = lean_ctor_get(x_271, 2);
x_288 = lean_ctor_get(x_271, 3);
x_289 = 1;
lean_inc(x_193);
lean_ctor_set(x_271, 3, x_193);
lean_ctor_set(x_271, 2, x_35);
lean_ctor_set(x_271, 1, x_34);
lean_ctor_set(x_271, 0, x_33);
x_290 = !lean_is_exclusive(x_193);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_291 = lean_ctor_get(x_193, 3);
lean_dec(x_291);
x_292 = lean_ctor_get(x_193, 2);
lean_dec(x_292);
x_293 = lean_ctor_get(x_193, 1);
lean_dec(x_293);
x_294 = lean_ctor_get(x_193, 0);
lean_dec(x_294);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_289);
lean_ctor_set(x_193, 3, x_288);
lean_ctor_set(x_193, 2, x_287);
lean_ctor_set(x_193, 1, x_286);
lean_ctor_set(x_193, 0, x_285);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_289);
x_295 = 0;
lean_ctor_set(x_191, 3, x_193);
lean_ctor_set(x_191, 0, x_271);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_295);
return x_191;
}
else
{
lean_object* x_296; uint8_t x_297; 
lean_dec(x_193);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_289);
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_285);
lean_ctor_set(x_296, 1, x_286);
lean_ctor_set(x_296, 2, x_287);
lean_ctor_set(x_296, 3, x_288);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_289);
x_297 = 0;
lean_ctor_set(x_191, 3, x_296);
lean_ctor_set(x_191, 0, x_271);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_297);
return x_191;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_298 = lean_ctor_get(x_271, 0);
x_299 = lean_ctor_get(x_271, 1);
x_300 = lean_ctor_get(x_271, 2);
x_301 = lean_ctor_get(x_271, 3);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_271);
x_302 = 1;
lean_inc(x_193);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_33);
lean_ctor_set(x_303, 1, x_34);
lean_ctor_set(x_303, 2, x_35);
lean_ctor_set(x_303, 3, x_193);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_304 = x_193;
} else {
 lean_dec_ref(x_193);
 x_304 = lean_box(0);
}
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_302);
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 4, 1);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_298);
lean_ctor_set(x_305, 1, x_299);
lean_ctor_set(x_305, 2, x_300);
lean_ctor_set(x_305, 3, x_301);
lean_ctor_set_uint8(x_305, sizeof(void*)*4, x_302);
x_306 = 0;
lean_ctor_set(x_191, 3, x_305);
lean_ctor_set(x_191, 0, x_303);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_306);
return x_191;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; 
x_307 = lean_ctor_get(x_191, 1);
x_308 = lean_ctor_get(x_191, 2);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_191);
x_309 = lean_ctor_get(x_271, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_271, 1);
lean_inc(x_310);
x_311 = lean_ctor_get(x_271, 2);
lean_inc(x_311);
x_312 = lean_ctor_get(x_271, 3);
lean_inc(x_312);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 lean_ctor_release(x_271, 3);
 x_313 = x_271;
} else {
 lean_dec_ref(x_271);
 x_313 = lean_box(0);
}
x_314 = 1;
lean_inc(x_193);
if (lean_is_scalar(x_313)) {
 x_315 = lean_alloc_ctor(1, 4, 1);
} else {
 x_315 = x_313;
}
lean_ctor_set(x_315, 0, x_33);
lean_ctor_set(x_315, 1, x_34);
lean_ctor_set(x_315, 2, x_35);
lean_ctor_set(x_315, 3, x_193);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_316 = x_193;
} else {
 lean_dec_ref(x_193);
 x_316 = lean_box(0);
}
lean_ctor_set_uint8(x_315, sizeof(void*)*4, x_314);
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 4, 1);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_310);
lean_ctor_set(x_317, 2, x_311);
lean_ctor_set(x_317, 3, x_312);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_314);
x_318 = 0;
x_319 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_319, 0, x_315);
lean_ctor_set(x_319, 1, x_307);
lean_ctor_set(x_319, 2, x_308);
lean_ctor_set(x_319, 3, x_317);
lean_ctor_set_uint8(x_319, sizeof(void*)*4, x_318);
return x_319;
}
}
else
{
uint8_t x_320; 
x_320 = !lean_is_exclusive(x_191);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_321 = lean_ctor_get(x_191, 3);
lean_dec(x_321);
x_322 = lean_ctor_get(x_191, 0);
lean_dec(x_322);
x_323 = !lean_is_exclusive(x_193);
if (x_323 == 0)
{
uint8_t x_324; 
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_280);
x_324 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_324);
return x_1;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_325 = lean_ctor_get(x_193, 0);
x_326 = lean_ctor_get(x_193, 1);
x_327 = lean_ctor_get(x_193, 2);
x_328 = lean_ctor_get(x_193, 3);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_193);
x_329 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_329, 0, x_325);
lean_ctor_set(x_329, 1, x_326);
lean_ctor_set(x_329, 2, x_327);
lean_ctor_set(x_329, 3, x_328);
lean_ctor_set_uint8(x_329, sizeof(void*)*4, x_280);
lean_ctor_set(x_191, 0, x_329);
x_330 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_330);
return x_1;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_331 = lean_ctor_get(x_191, 1);
x_332 = lean_ctor_get(x_191, 2);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_191);
x_333 = lean_ctor_get(x_193, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_193, 1);
lean_inc(x_334);
x_335 = lean_ctor_get(x_193, 2);
lean_inc(x_335);
x_336 = lean_ctor_get(x_193, 3);
lean_inc(x_336);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_337 = x_193;
} else {
 lean_dec_ref(x_193);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_334);
lean_ctor_set(x_338, 2, x_335);
lean_ctor_set(x_338, 3, x_336);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_280);
x_339 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_331);
lean_ctor_set(x_339, 2, x_332);
lean_ctor_set(x_339, 3, x_271);
lean_ctor_set_uint8(x_339, sizeof(void*)*4, x_192);
x_340 = 1;
lean_ctor_set(x_1, 3, x_339);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_340);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_341; 
x_341 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_341);
return x_1;
}
}
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_342 = lean_ctor_get(x_1, 0);
x_343 = lean_ctor_get(x_1, 1);
x_344 = lean_ctor_get(x_1, 2);
x_345 = lean_ctor_get(x_1, 3);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_1);
x_346 = l_Lean_Name_quickCmp(x_2, x_343);
switch (x_346) {
case 0:
{
lean_object* x_347; uint8_t x_348; 
x_347 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_342, x_2, x_3);
x_348 = lean_ctor_get_uint8(x_347, sizeof(void*)*4);
if (x_348 == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_347, 0);
lean_inc(x_349);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; 
x_350 = lean_ctor_get(x_347, 3);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; 
x_351 = lean_ctor_get(x_347, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_347, 2);
lean_inc(x_352);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_353 = x_347;
} else {
 lean_dec_ref(x_347);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 4, 1);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_350);
lean_ctor_set(x_354, 1, x_351);
lean_ctor_set(x_354, 2, x_352);
lean_ctor_set(x_354, 3, x_350);
lean_ctor_set_uint8(x_354, sizeof(void*)*4, x_348);
x_355 = 1;
x_356 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_343);
lean_ctor_set(x_356, 2, x_344);
lean_ctor_set(x_356, 3, x_345);
lean_ctor_set_uint8(x_356, sizeof(void*)*4, x_355);
return x_356;
}
else
{
uint8_t x_357; 
x_357 = lean_ctor_get_uint8(x_350, sizeof(void*)*4);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_358 = lean_ctor_get(x_347, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_347, 2);
lean_inc(x_359);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_360 = x_347;
} else {
 lean_dec_ref(x_347);
 x_360 = lean_box(0);
}
x_361 = lean_ctor_get(x_350, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_350, 1);
lean_inc(x_362);
x_363 = lean_ctor_get(x_350, 2);
lean_inc(x_363);
x_364 = lean_ctor_get(x_350, 3);
lean_inc(x_364);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_365 = x_350;
} else {
 lean_dec_ref(x_350);
 x_365 = lean_box(0);
}
x_366 = 1;
if (lean_is_scalar(x_365)) {
 x_367 = lean_alloc_ctor(1, 4, 1);
} else {
 x_367 = x_365;
}
lean_ctor_set(x_367, 0, x_349);
lean_ctor_set(x_367, 1, x_358);
lean_ctor_set(x_367, 2, x_359);
lean_ctor_set(x_367, 3, x_361);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_366);
if (lean_is_scalar(x_360)) {
 x_368 = lean_alloc_ctor(1, 4, 1);
} else {
 x_368 = x_360;
}
lean_ctor_set(x_368, 0, x_364);
lean_ctor_set(x_368, 1, x_343);
lean_ctor_set(x_368, 2, x_344);
lean_ctor_set(x_368, 3, x_345);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_366);
x_369 = 0;
x_370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_362);
lean_ctor_set(x_370, 2, x_363);
lean_ctor_set(x_370, 3, x_368);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_369);
return x_370;
}
else
{
lean_object* x_371; uint8_t x_372; lean_object* x_373; 
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_371 = x_350;
} else {
 lean_dec_ref(x_350);
 x_371 = lean_box(0);
}
x_372 = 1;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_347);
lean_ctor_set(x_373, 1, x_343);
lean_ctor_set(x_373, 2, x_344);
lean_ctor_set(x_373, 3, x_345);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
return x_373;
}
}
}
else
{
uint8_t x_374; 
x_374 = lean_ctor_get_uint8(x_349, sizeof(void*)*4);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; 
x_375 = lean_ctor_get(x_347, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_347, 2);
lean_inc(x_376);
x_377 = lean_ctor_get(x_347, 3);
lean_inc(x_377);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_378 = x_347;
} else {
 lean_dec_ref(x_347);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_349, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_349, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_349, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_349, 3);
lean_inc(x_382);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_383 = x_349;
} else {
 lean_dec_ref(x_349);
 x_383 = lean_box(0);
}
x_384 = 1;
if (lean_is_scalar(x_383)) {
 x_385 = lean_alloc_ctor(1, 4, 1);
} else {
 x_385 = x_383;
}
lean_ctor_set(x_385, 0, x_379);
lean_ctor_set(x_385, 1, x_380);
lean_ctor_set(x_385, 2, x_381);
lean_ctor_set(x_385, 3, x_382);
lean_ctor_set_uint8(x_385, sizeof(void*)*4, x_384);
if (lean_is_scalar(x_378)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_378;
}
lean_ctor_set(x_386, 0, x_377);
lean_ctor_set(x_386, 1, x_343);
lean_ctor_set(x_386, 2, x_344);
lean_ctor_set(x_386, 3, x_345);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_384);
x_387 = 0;
x_388 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_375);
lean_ctor_set(x_388, 2, x_376);
lean_ctor_set(x_388, 3, x_386);
lean_ctor_set_uint8(x_388, sizeof(void*)*4, x_387);
return x_388;
}
else
{
lean_object* x_389; 
x_389 = lean_ctor_get(x_347, 3);
lean_inc(x_389);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; uint8_t x_391; lean_object* x_392; 
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_390 = x_349;
} else {
 lean_dec_ref(x_349);
 x_390 = lean_box(0);
}
x_391 = 1;
if (lean_is_scalar(x_390)) {
 x_392 = lean_alloc_ctor(1, 4, 1);
} else {
 x_392 = x_390;
}
lean_ctor_set(x_392, 0, x_347);
lean_ctor_set(x_392, 1, x_343);
lean_ctor_set(x_392, 2, x_344);
lean_ctor_set(x_392, 3, x_345);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_391);
return x_392;
}
else
{
uint8_t x_393; 
x_393 = lean_ctor_get_uint8(x_389, sizeof(void*)*4);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; 
x_394 = lean_ctor_get(x_347, 1);
lean_inc(x_394);
x_395 = lean_ctor_get(x_347, 2);
lean_inc(x_395);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_396 = x_347;
} else {
 lean_dec_ref(x_347);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_389, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_389, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_389, 2);
lean_inc(x_399);
x_400 = lean_ctor_get(x_389, 3);
lean_inc(x_400);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 lean_ctor_release(x_389, 2);
 lean_ctor_release(x_389, 3);
 x_401 = x_389;
} else {
 lean_dec_ref(x_389);
 x_401 = lean_box(0);
}
x_402 = 1;
lean_inc(x_349);
if (lean_is_scalar(x_401)) {
 x_403 = lean_alloc_ctor(1, 4, 1);
} else {
 x_403 = x_401;
}
lean_ctor_set(x_403, 0, x_349);
lean_ctor_set(x_403, 1, x_394);
lean_ctor_set(x_403, 2, x_395);
lean_ctor_set(x_403, 3, x_397);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_404 = x_349;
} else {
 lean_dec_ref(x_349);
 x_404 = lean_box(0);
}
lean_ctor_set_uint8(x_403, sizeof(void*)*4, x_402);
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(1, 4, 1);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_400);
lean_ctor_set(x_405, 1, x_343);
lean_ctor_set(x_405, 2, x_344);
lean_ctor_set(x_405, 3, x_345);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_402);
x_406 = 0;
if (lean_is_scalar(x_396)) {
 x_407 = lean_alloc_ctor(1, 4, 1);
} else {
 x_407 = x_396;
}
lean_ctor_set(x_407, 0, x_403);
lean_ctor_set(x_407, 1, x_398);
lean_ctor_set(x_407, 2, x_399);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
return x_407;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; 
x_408 = lean_ctor_get(x_347, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_347, 2);
lean_inc(x_409);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_410 = x_347;
} else {
 lean_dec_ref(x_347);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_349, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_349, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_349, 2);
lean_inc(x_413);
x_414 = lean_ctor_get(x_349, 3);
lean_inc(x_414);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_415 = x_349;
} else {
 lean_dec_ref(x_349);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(1, 4, 1);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_411);
lean_ctor_set(x_416, 1, x_412);
lean_ctor_set(x_416, 2, x_413);
lean_ctor_set(x_416, 3, x_414);
lean_ctor_set_uint8(x_416, sizeof(void*)*4, x_393);
if (lean_is_scalar(x_410)) {
 x_417 = lean_alloc_ctor(1, 4, 1);
} else {
 x_417 = x_410;
}
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_408);
lean_ctor_set(x_417, 2, x_409);
lean_ctor_set(x_417, 3, x_389);
lean_ctor_set_uint8(x_417, sizeof(void*)*4, x_348);
x_418 = 1;
x_419 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_343);
lean_ctor_set(x_419, 2, x_344);
lean_ctor_set(x_419, 3, x_345);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
return x_419;
}
}
}
}
}
else
{
uint8_t x_420; lean_object* x_421; 
x_420 = 1;
x_421 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_421, 0, x_347);
lean_ctor_set(x_421, 1, x_343);
lean_ctor_set(x_421, 2, x_344);
lean_ctor_set(x_421, 3, x_345);
lean_ctor_set_uint8(x_421, sizeof(void*)*4, x_420);
return x_421;
}
}
case 1:
{
uint8_t x_422; lean_object* x_423; 
lean_dec(x_344);
lean_dec(x_343);
x_422 = 1;
x_423 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_423, 0, x_342);
lean_ctor_set(x_423, 1, x_2);
lean_ctor_set(x_423, 2, x_3);
lean_ctor_set(x_423, 3, x_345);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
return x_423;
}
default: 
{
lean_object* x_424; uint8_t x_425; 
x_424 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_345, x_2, x_3);
x_425 = lean_ctor_get_uint8(x_424, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; 
x_426 = lean_ctor_get(x_424, 0);
lean_inc(x_426);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; 
x_427 = lean_ctor_get(x_424, 3);
lean_inc(x_427);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; 
x_428 = lean_ctor_get(x_424, 1);
lean_inc(x_428);
x_429 = lean_ctor_get(x_424, 2);
lean_inc(x_429);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_430 = x_424;
} else {
 lean_dec_ref(x_424);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 4, 1);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_427);
lean_ctor_set(x_431, 1, x_428);
lean_ctor_set(x_431, 2, x_429);
lean_ctor_set(x_431, 3, x_427);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_425);
x_432 = 1;
x_433 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_433, 0, x_342);
lean_ctor_set(x_433, 1, x_343);
lean_ctor_set(x_433, 2, x_344);
lean_ctor_set(x_433, 3, x_431);
lean_ctor_set_uint8(x_433, sizeof(void*)*4, x_432);
return x_433;
}
else
{
uint8_t x_434; 
x_434 = lean_ctor_get_uint8(x_427, sizeof(void*)*4);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; 
x_435 = lean_ctor_get(x_424, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_424, 2);
lean_inc(x_436);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_437 = x_424;
} else {
 lean_dec_ref(x_424);
 x_437 = lean_box(0);
}
x_438 = lean_ctor_get(x_427, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_427, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_427, 2);
lean_inc(x_440);
x_441 = lean_ctor_get(x_427, 3);
lean_inc(x_441);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_442 = x_427;
} else {
 lean_dec_ref(x_427);
 x_442 = lean_box(0);
}
x_443 = 1;
if (lean_is_scalar(x_442)) {
 x_444 = lean_alloc_ctor(1, 4, 1);
} else {
 x_444 = x_442;
}
lean_ctor_set(x_444, 0, x_342);
lean_ctor_set(x_444, 1, x_343);
lean_ctor_set(x_444, 2, x_344);
lean_ctor_set(x_444, 3, x_426);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_443);
if (lean_is_scalar(x_437)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_437;
}
lean_ctor_set(x_445, 0, x_438);
lean_ctor_set(x_445, 1, x_439);
lean_ctor_set(x_445, 2, x_440);
lean_ctor_set(x_445, 3, x_441);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_443);
x_446 = 0;
x_447 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_447, 0, x_444);
lean_ctor_set(x_447, 1, x_435);
lean_ctor_set(x_447, 2, x_436);
lean_ctor_set(x_447, 3, x_445);
lean_ctor_set_uint8(x_447, sizeof(void*)*4, x_446);
return x_447;
}
else
{
lean_object* x_448; uint8_t x_449; lean_object* x_450; 
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_448 = x_427;
} else {
 lean_dec_ref(x_427);
 x_448 = lean_box(0);
}
x_449 = 1;
if (lean_is_scalar(x_448)) {
 x_450 = lean_alloc_ctor(1, 4, 1);
} else {
 x_450 = x_448;
}
lean_ctor_set(x_450, 0, x_342);
lean_ctor_set(x_450, 1, x_343);
lean_ctor_set(x_450, 2, x_344);
lean_ctor_set(x_450, 3, x_424);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
return x_450;
}
}
}
else
{
uint8_t x_451; 
x_451 = lean_ctor_get_uint8(x_426, sizeof(void*)*4);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; lean_object* x_465; 
x_452 = lean_ctor_get(x_424, 1);
lean_inc(x_452);
x_453 = lean_ctor_get(x_424, 2);
lean_inc(x_453);
x_454 = lean_ctor_get(x_424, 3);
lean_inc(x_454);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_455 = x_424;
} else {
 lean_dec_ref(x_424);
 x_455 = lean_box(0);
}
x_456 = lean_ctor_get(x_426, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_426, 1);
lean_inc(x_457);
x_458 = lean_ctor_get(x_426, 2);
lean_inc(x_458);
x_459 = lean_ctor_get(x_426, 3);
lean_inc(x_459);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_460 = x_426;
} else {
 lean_dec_ref(x_426);
 x_460 = lean_box(0);
}
x_461 = 1;
if (lean_is_scalar(x_460)) {
 x_462 = lean_alloc_ctor(1, 4, 1);
} else {
 x_462 = x_460;
}
lean_ctor_set(x_462, 0, x_342);
lean_ctor_set(x_462, 1, x_343);
lean_ctor_set(x_462, 2, x_344);
lean_ctor_set(x_462, 3, x_456);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
if (lean_is_scalar(x_455)) {
 x_463 = lean_alloc_ctor(1, 4, 1);
} else {
 x_463 = x_455;
}
lean_ctor_set(x_463, 0, x_459);
lean_ctor_set(x_463, 1, x_452);
lean_ctor_set(x_463, 2, x_453);
lean_ctor_set(x_463, 3, x_454);
lean_ctor_set_uint8(x_463, sizeof(void*)*4, x_461);
x_464 = 0;
x_465 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_457);
lean_ctor_set(x_465, 2, x_458);
lean_ctor_set(x_465, 3, x_463);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_464);
return x_465;
}
else
{
lean_object* x_466; 
x_466 = lean_ctor_get(x_424, 3);
lean_inc(x_466);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; uint8_t x_468; lean_object* x_469; 
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_467 = x_426;
} else {
 lean_dec_ref(x_426);
 x_467 = lean_box(0);
}
x_468 = 1;
if (lean_is_scalar(x_467)) {
 x_469 = lean_alloc_ctor(1, 4, 1);
} else {
 x_469 = x_467;
}
lean_ctor_set(x_469, 0, x_342);
lean_ctor_set(x_469, 1, x_343);
lean_ctor_set(x_469, 2, x_344);
lean_ctor_set(x_469, 3, x_424);
lean_ctor_set_uint8(x_469, sizeof(void*)*4, x_468);
return x_469;
}
else
{
uint8_t x_470; 
x_470 = lean_ctor_get_uint8(x_466, sizeof(void*)*4);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; lean_object* x_484; 
x_471 = lean_ctor_get(x_424, 1);
lean_inc(x_471);
x_472 = lean_ctor_get(x_424, 2);
lean_inc(x_472);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_473 = x_424;
} else {
 lean_dec_ref(x_424);
 x_473 = lean_box(0);
}
x_474 = lean_ctor_get(x_466, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_466, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_466, 2);
lean_inc(x_476);
x_477 = lean_ctor_get(x_466, 3);
lean_inc(x_477);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 lean_ctor_release(x_466, 2);
 lean_ctor_release(x_466, 3);
 x_478 = x_466;
} else {
 lean_dec_ref(x_466);
 x_478 = lean_box(0);
}
x_479 = 1;
lean_inc(x_426);
if (lean_is_scalar(x_478)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_478;
}
lean_ctor_set(x_480, 0, x_342);
lean_ctor_set(x_480, 1, x_343);
lean_ctor_set(x_480, 2, x_344);
lean_ctor_set(x_480, 3, x_426);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_481 = x_426;
} else {
 lean_dec_ref(x_426);
 x_481 = lean_box(0);
}
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_479);
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(1, 4, 1);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_474);
lean_ctor_set(x_482, 1, x_475);
lean_ctor_set(x_482, 2, x_476);
lean_ctor_set(x_482, 3, x_477);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_479);
x_483 = 0;
if (lean_is_scalar(x_473)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_473;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_471);
lean_ctor_set(x_484, 2, x_472);
lean_ctor_set(x_484, 3, x_482);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_483);
return x_484;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; lean_object* x_496; 
x_485 = lean_ctor_get(x_424, 1);
lean_inc(x_485);
x_486 = lean_ctor_get(x_424, 2);
lean_inc(x_486);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_487 = x_424;
} else {
 lean_dec_ref(x_424);
 x_487 = lean_box(0);
}
x_488 = lean_ctor_get(x_426, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_426, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_426, 2);
lean_inc(x_490);
x_491 = lean_ctor_get(x_426, 3);
lean_inc(x_491);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_492 = x_426;
} else {
 lean_dec_ref(x_426);
 x_492 = lean_box(0);
}
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(1, 4, 1);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_488);
lean_ctor_set(x_493, 1, x_489);
lean_ctor_set(x_493, 2, x_490);
lean_ctor_set(x_493, 3, x_491);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_470);
if (lean_is_scalar(x_487)) {
 x_494 = lean_alloc_ctor(1, 4, 1);
} else {
 x_494 = x_487;
}
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_485);
lean_ctor_set(x_494, 2, x_486);
lean_ctor_set(x_494, 3, x_466);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_425);
x_495 = 1;
x_496 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_496, 0, x_342);
lean_ctor_set(x_496, 1, x_343);
lean_ctor_set(x_496, 2, x_344);
lean_ctor_set(x_496, 3, x_494);
lean_ctor_set_uint8(x_496, sizeof(void*)*4, x_495);
return x_496;
}
}
}
}
}
else
{
uint8_t x_497; lean_object* x_498; 
x_497 = 1;
x_498 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_498, 0, x_342);
lean_ctor_set(x_498, 1, x_343);
lean_ctor_set(x_498, 2, x_344);
lean_ctor_set(x_498, 3, x_424);
lean_ctor_set_uint8(x_498, sizeof(void*)*4, x_497);
return x_498;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_14 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_9, x_2, x_3);
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
x_17 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_12, x_2, x_3);
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
x_24 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_19, x_2, x_3);
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
x_29 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_22, x_2, x_3);
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
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_33, x_2, x_3);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*4);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_38, 3);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_38, 3);
lean_dec(x_43);
x_44 = lean_ctor_get(x_38, 0);
lean_dec(x_44);
lean_ctor_set(x_38, 0, x_41);
x_45 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_38, 1);
x_47 = lean_ctor_get(x_38, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_39);
x_49 = 1;
lean_ctor_set(x_1, 0, x_48);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_41, sizeof(void*)*4);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_38, 1);
x_53 = lean_ctor_get(x_38, 2);
x_54 = lean_ctor_get(x_38, 3);
lean_dec(x_54);
x_55 = lean_ctor_get(x_38, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_41);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_41, 0);
x_58 = lean_ctor_get(x_41, 1);
x_59 = lean_ctor_get(x_41, 2);
x_60 = lean_ctor_get(x_41, 3);
x_61 = 1;
lean_ctor_set(x_41, 3, x_57);
lean_ctor_set(x_41, 2, x_53);
lean_ctor_set(x_41, 1, x_52);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_61);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_60);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_61);
x_62 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_59);
lean_ctor_set(x_1, 1, x_58);
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_62);
return x_1;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; uint8_t x_69; 
x_63 = lean_ctor_get(x_41, 0);
x_64 = lean_ctor_get(x_41, 1);
x_65 = lean_ctor_get(x_41, 2);
x_66 = lean_ctor_get(x_41, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_41);
x_67 = 1;
x_68 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_68, 0, x_40);
lean_ctor_set(x_68, 1, x_52);
lean_ctor_set(x_68, 2, x_53);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set_uint8(x_68, sizeof(void*)*4, x_67);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_66);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_67);
x_69 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_65);
lean_ctor_set(x_1, 1, x_64);
lean_ctor_set(x_1, 0, x_68);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_70 = lean_ctor_get(x_38, 1);
x_71 = lean_ctor_get(x_38, 2);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_38);
x_72 = lean_ctor_get(x_41, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_41, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_41, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_41, 3);
lean_inc(x_75);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_76 = x_41;
} else {
 lean_dec_ref(x_41);
 x_76 = lean_box(0);
}
x_77 = 1;
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(1, 4, 1);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_40);
lean_ctor_set(x_78, 1, x_70);
lean_ctor_set(x_78, 2, x_71);
lean_ctor_set(x_78, 3, x_72);
lean_ctor_set_uint8(x_78, sizeof(void*)*4, x_77);
x_79 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_34);
lean_ctor_set(x_79, 2, x_35);
lean_ctor_set(x_79, 3, x_36);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_77);
x_80 = 0;
lean_ctor_set(x_1, 3, x_79);
lean_ctor_set(x_1, 2, x_74);
lean_ctor_set(x_1, 1, x_73);
lean_ctor_set(x_1, 0, x_78);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_80);
return x_1;
}
}
else
{
uint8_t x_81; 
lean_free_object(x_1);
x_81 = !lean_is_exclusive(x_41);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_41, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_41, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_41, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_41, 0);
lean_dec(x_85);
x_86 = 1;
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_86);
return x_41;
}
else
{
uint8_t x_87; lean_object* x_88; 
lean_dec(x_41);
x_87 = 1;
x_88 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_88, 0, x_38);
lean_ctor_set(x_88, 1, x_34);
lean_ctor_set(x_88, 2, x_35);
lean_ctor_set(x_88, 3, x_36);
lean_ctor_set_uint8(x_88, sizeof(void*)*4, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
x_89 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_38);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_91 = lean_ctor_get(x_38, 1);
x_92 = lean_ctor_get(x_38, 2);
x_93 = lean_ctor_get(x_38, 3);
x_94 = lean_ctor_get(x_38, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_40);
if (x_95 == 0)
{
uint8_t x_96; uint8_t x_97; 
x_96 = 1;
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_96);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_93);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_96);
x_97 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_92);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_40);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_97);
return x_1;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; uint8_t x_104; 
x_98 = lean_ctor_get(x_40, 0);
x_99 = lean_ctor_get(x_40, 1);
x_100 = lean_ctor_get(x_40, 2);
x_101 = lean_ctor_get(x_40, 3);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_40);
x_102 = 1;
x_103 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_99);
lean_ctor_set(x_103, 2, x_100);
lean_ctor_set(x_103, 3, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*4, x_102);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_93);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_102);
x_104 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_92);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_103);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_104);
return x_1;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_105 = lean_ctor_get(x_38, 1);
x_106 = lean_ctor_get(x_38, 2);
x_107 = lean_ctor_get(x_38, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_38);
x_108 = lean_ctor_get(x_40, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_40, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_40, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_40, 3);
lean_inc(x_111);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_112 = x_40;
} else {
 lean_dec_ref(x_40);
 x_112 = lean_box(0);
}
x_113 = 1;
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(1, 4, 1);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_109);
lean_ctor_set(x_114, 2, x_110);
lean_ctor_set(x_114, 3, x_111);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_113);
x_115 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_34);
lean_ctor_set(x_115, 2, x_35);
lean_ctor_set(x_115, 3, x_36);
lean_ctor_set_uint8(x_115, sizeof(void*)*4, x_113);
x_116 = 0;
lean_ctor_set(x_1, 3, x_115);
lean_ctor_set(x_1, 2, x_106);
lean_ctor_set(x_1, 1, x_105);
lean_ctor_set(x_1, 0, x_114);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_116);
return x_1;
}
}
else
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_38, 3);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
lean_free_object(x_1);
x_118 = !lean_is_exclusive(x_40);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_119 = lean_ctor_get(x_40, 3);
lean_dec(x_119);
x_120 = lean_ctor_get(x_40, 2);
lean_dec(x_120);
x_121 = lean_ctor_get(x_40, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_40, 0);
lean_dec(x_122);
x_123 = 1;
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_123);
return x_40;
}
else
{
uint8_t x_124; lean_object* x_125; 
lean_dec(x_40);
x_124 = 1;
x_125 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_125, 0, x_38);
lean_ctor_set(x_125, 1, x_34);
lean_ctor_set(x_125, 2, x_35);
lean_ctor_set(x_125, 3, x_36);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_124);
return x_125;
}
}
else
{
uint8_t x_126; 
x_126 = lean_ctor_get_uint8(x_117, sizeof(void*)*4);
if (x_126 == 0)
{
uint8_t x_127; 
lean_free_object(x_1);
x_127 = !lean_is_exclusive(x_38);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_38, 1);
x_129 = lean_ctor_get(x_38, 2);
x_130 = lean_ctor_get(x_38, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_38, 0);
lean_dec(x_131);
x_132 = !lean_is_exclusive(x_117);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; 
x_133 = lean_ctor_get(x_117, 0);
x_134 = lean_ctor_get(x_117, 1);
x_135 = lean_ctor_get(x_117, 2);
x_136 = lean_ctor_get(x_117, 3);
x_137 = 1;
lean_inc(x_40);
lean_ctor_set(x_117, 3, x_133);
lean_ctor_set(x_117, 2, x_129);
lean_ctor_set(x_117, 1, x_128);
lean_ctor_set(x_117, 0, x_40);
x_138 = !lean_is_exclusive(x_40);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_139 = lean_ctor_get(x_40, 3);
lean_dec(x_139);
x_140 = lean_ctor_get(x_40, 2);
lean_dec(x_140);
x_141 = lean_ctor_get(x_40, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_40, 0);
lean_dec(x_142);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_137);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 0, x_136);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_137);
x_143 = 0;
lean_ctor_set(x_38, 3, x_40);
lean_ctor_set(x_38, 2, x_135);
lean_ctor_set(x_38, 1, x_134);
lean_ctor_set(x_38, 0, x_117);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_143);
return x_38;
}
else
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_40);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_137);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_136);
lean_ctor_set(x_144, 1, x_34);
lean_ctor_set(x_144, 2, x_35);
lean_ctor_set(x_144, 3, x_36);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_137);
x_145 = 0;
lean_ctor_set(x_38, 3, x_144);
lean_ctor_set(x_38, 2, x_135);
lean_ctor_set(x_38, 1, x_134);
lean_ctor_set(x_38, 0, x_117);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_145);
return x_38;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_146 = lean_ctor_get(x_117, 0);
x_147 = lean_ctor_get(x_117, 1);
x_148 = lean_ctor_get(x_117, 2);
x_149 = lean_ctor_get(x_117, 3);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_117);
x_150 = 1;
lean_inc(x_40);
x_151 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_151, 0, x_40);
lean_ctor_set(x_151, 1, x_128);
lean_ctor_set(x_151, 2, x_129);
lean_ctor_set(x_151, 3, x_146);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_152 = x_40;
} else {
 lean_dec_ref(x_40);
 x_152 = lean_box(0);
}
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_150);
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 4, 1);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_34);
lean_ctor_set(x_153, 2, x_35);
lean_ctor_set(x_153, 3, x_36);
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_150);
x_154 = 0;
lean_ctor_set(x_38, 3, x_153);
lean_ctor_set(x_38, 2, x_148);
lean_ctor_set(x_38, 1, x_147);
lean_ctor_set(x_38, 0, x_151);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_154);
return x_38;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; 
x_155 = lean_ctor_get(x_38, 1);
x_156 = lean_ctor_get(x_38, 2);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_38);
x_157 = lean_ctor_get(x_117, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_117, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_117, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_117, 3);
lean_inc(x_160);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 x_161 = x_117;
} else {
 lean_dec_ref(x_117);
 x_161 = lean_box(0);
}
x_162 = 1;
lean_inc(x_40);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(1, 4, 1);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_40);
lean_ctor_set(x_163, 1, x_155);
lean_ctor_set(x_163, 2, x_156);
lean_ctor_set(x_163, 3, x_157);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_164 = x_40;
} else {
 lean_dec_ref(x_40);
 x_164 = lean_box(0);
}
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_162);
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 4, 1);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_160);
lean_ctor_set(x_165, 1, x_34);
lean_ctor_set(x_165, 2, x_35);
lean_ctor_set(x_165, 3, x_36);
lean_ctor_set_uint8(x_165, sizeof(void*)*4, x_162);
x_166 = 0;
x_167 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_167, 0, x_163);
lean_ctor_set(x_167, 1, x_158);
lean_ctor_set(x_167, 2, x_159);
lean_ctor_set(x_167, 3, x_165);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_166);
return x_167;
}
}
else
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_38);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_ctor_get(x_38, 3);
lean_dec(x_169);
x_170 = lean_ctor_get(x_38, 0);
lean_dec(x_170);
x_171 = !lean_is_exclusive(x_40);
if (x_171 == 0)
{
uint8_t x_172; 
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_126);
x_172 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_172);
return x_1;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_173 = lean_ctor_get(x_40, 0);
x_174 = lean_ctor_get(x_40, 1);
x_175 = lean_ctor_get(x_40, 2);
x_176 = lean_ctor_get(x_40, 3);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_40);
x_177 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_174);
lean_ctor_set(x_177, 2, x_175);
lean_ctor_set(x_177, 3, x_176);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_126);
lean_ctor_set(x_38, 0, x_177);
x_178 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_178);
return x_1;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_179 = lean_ctor_get(x_38, 1);
x_180 = lean_ctor_get(x_38, 2);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_38);
x_181 = lean_ctor_get(x_40, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_40, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_40, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_40, 3);
lean_inc(x_184);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_185 = x_40;
} else {
 lean_dec_ref(x_40);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 4, 1);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_181);
lean_ctor_set(x_186, 1, x_182);
lean_ctor_set(x_186, 2, x_183);
lean_ctor_set(x_186, 3, x_184);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_126);
x_187 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_179);
lean_ctor_set(x_187, 2, x_180);
lean_ctor_set(x_187, 3, x_117);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_39);
x_188 = 1;
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_189; 
x_189 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
case 1:
{
uint8_t x_190; 
lean_dec(x_35);
lean_dec(x_34);
x_190 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_190);
return x_1;
}
default: 
{
lean_object* x_191; uint8_t x_192; 
x_191 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_36, x_2, x_3);
x_192 = lean_ctor_get_uint8(x_191, sizeof(void*)*4);
if (x_192 == 0)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_191, 3);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_191);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_196 = lean_ctor_get(x_191, 3);
lean_dec(x_196);
x_197 = lean_ctor_get(x_191, 0);
lean_dec(x_197);
lean_ctor_set(x_191, 0, x_194);
x_198 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_198);
return x_1;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_199 = lean_ctor_get(x_191, 1);
x_200 = lean_ctor_get(x_191, 2);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_191);
x_201 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_201, 0, x_194);
lean_ctor_set(x_201, 1, x_199);
lean_ctor_set(x_201, 2, x_200);
lean_ctor_set(x_201, 3, x_194);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_192);
x_202 = 1;
lean_ctor_set(x_1, 3, x_201);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
}
}
else
{
uint8_t x_203; 
x_203 = lean_ctor_get_uint8(x_194, sizeof(void*)*4);
if (x_203 == 0)
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_191);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_191, 1);
x_206 = lean_ctor_get(x_191, 2);
x_207 = lean_ctor_get(x_191, 3);
lean_dec(x_207);
x_208 = lean_ctor_get(x_191, 0);
lean_dec(x_208);
x_209 = !lean_is_exclusive(x_194);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; 
x_210 = lean_ctor_get(x_194, 0);
x_211 = lean_ctor_get(x_194, 1);
x_212 = lean_ctor_get(x_194, 2);
x_213 = lean_ctor_get(x_194, 3);
x_214 = 1;
lean_ctor_set(x_194, 3, x_193);
lean_ctor_set(x_194, 2, x_35);
lean_ctor_set(x_194, 1, x_34);
lean_ctor_set(x_194, 0, x_33);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_214);
lean_ctor_set(x_191, 3, x_213);
lean_ctor_set(x_191, 2, x_212);
lean_ctor_set(x_191, 1, x_211);
lean_ctor_set(x_191, 0, x_210);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_214);
x_215 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_215);
return x_1;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; uint8_t x_222; 
x_216 = lean_ctor_get(x_194, 0);
x_217 = lean_ctor_get(x_194, 1);
x_218 = lean_ctor_get(x_194, 2);
x_219 = lean_ctor_get(x_194, 3);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_194);
x_220 = 1;
x_221 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_221, 0, x_33);
lean_ctor_set(x_221, 1, x_34);
lean_ctor_set(x_221, 2, x_35);
lean_ctor_set(x_221, 3, x_193);
lean_ctor_set_uint8(x_221, sizeof(void*)*4, x_220);
lean_ctor_set(x_191, 3, x_219);
lean_ctor_set(x_191, 2, x_218);
lean_ctor_set(x_191, 1, x_217);
lean_ctor_set(x_191, 0, x_216);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_220);
x_222 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_221);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_222);
return x_1;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_223 = lean_ctor_get(x_191, 1);
x_224 = lean_ctor_get(x_191, 2);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_191);
x_225 = lean_ctor_get(x_194, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_194, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_194, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_194, 3);
lean_inc(x_228);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_229 = x_194;
} else {
 lean_dec_ref(x_194);
 x_229 = lean_box(0);
}
x_230 = 1;
if (lean_is_scalar(x_229)) {
 x_231 = lean_alloc_ctor(1, 4, 1);
} else {
 x_231 = x_229;
}
lean_ctor_set(x_231, 0, x_33);
lean_ctor_set(x_231, 1, x_34);
lean_ctor_set(x_231, 2, x_35);
lean_ctor_set(x_231, 3, x_193);
lean_ctor_set_uint8(x_231, sizeof(void*)*4, x_230);
x_232 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_232, 0, x_225);
lean_ctor_set(x_232, 1, x_226);
lean_ctor_set(x_232, 2, x_227);
lean_ctor_set(x_232, 3, x_228);
lean_ctor_set_uint8(x_232, sizeof(void*)*4, x_230);
x_233 = 0;
lean_ctor_set(x_1, 3, x_232);
lean_ctor_set(x_1, 2, x_224);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_1, 0, x_231);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
}
else
{
uint8_t x_234; 
lean_free_object(x_1);
x_234 = !lean_is_exclusive(x_194);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_235 = lean_ctor_get(x_194, 3);
lean_dec(x_235);
x_236 = lean_ctor_get(x_194, 2);
lean_dec(x_236);
x_237 = lean_ctor_get(x_194, 1);
lean_dec(x_237);
x_238 = lean_ctor_get(x_194, 0);
lean_dec(x_238);
x_239 = 1;
lean_ctor_set(x_194, 3, x_191);
lean_ctor_set(x_194, 2, x_35);
lean_ctor_set(x_194, 1, x_34);
lean_ctor_set(x_194, 0, x_33);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_239);
return x_194;
}
else
{
uint8_t x_240; lean_object* x_241; 
lean_dec(x_194);
x_240 = 1;
x_241 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_241, 0, x_33);
lean_ctor_set(x_241, 1, x_34);
lean_ctor_set(x_241, 2, x_35);
lean_ctor_set(x_241, 3, x_191);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_240);
return x_241;
}
}
}
}
else
{
uint8_t x_242; 
x_242 = lean_ctor_get_uint8(x_193, sizeof(void*)*4);
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = !lean_is_exclusive(x_191);
if (x_243 == 0)
{
lean_object* x_244; uint8_t x_245; 
x_244 = lean_ctor_get(x_191, 0);
lean_dec(x_244);
x_245 = !lean_is_exclusive(x_193);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_251; 
x_246 = lean_ctor_get(x_193, 0);
x_247 = lean_ctor_get(x_193, 1);
x_248 = lean_ctor_get(x_193, 2);
x_249 = lean_ctor_get(x_193, 3);
x_250 = 1;
lean_ctor_set(x_193, 3, x_246);
lean_ctor_set(x_193, 2, x_35);
lean_ctor_set(x_193, 1, x_34);
lean_ctor_set(x_193, 0, x_33);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_250);
lean_ctor_set(x_191, 0, x_249);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_250);
x_251 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_248);
lean_ctor_set(x_1, 1, x_247);
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_251);
return x_1;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; uint8_t x_258; 
x_252 = lean_ctor_get(x_193, 0);
x_253 = lean_ctor_get(x_193, 1);
x_254 = lean_ctor_get(x_193, 2);
x_255 = lean_ctor_get(x_193, 3);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_193);
x_256 = 1;
x_257 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_257, 0, x_33);
lean_ctor_set(x_257, 1, x_34);
lean_ctor_set(x_257, 2, x_35);
lean_ctor_set(x_257, 3, x_252);
lean_ctor_set_uint8(x_257, sizeof(void*)*4, x_256);
lean_ctor_set(x_191, 0, x_255);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_256);
x_258 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_254);
lean_ctor_set(x_1, 1, x_253);
lean_ctor_set(x_1, 0, x_257);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_258);
return x_1;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_259 = lean_ctor_get(x_191, 1);
x_260 = lean_ctor_get(x_191, 2);
x_261 = lean_ctor_get(x_191, 3);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_191);
x_262 = lean_ctor_get(x_193, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_193, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_193, 2);
lean_inc(x_264);
x_265 = lean_ctor_get(x_193, 3);
lean_inc(x_265);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_266 = x_193;
} else {
 lean_dec_ref(x_193);
 x_266 = lean_box(0);
}
x_267 = 1;
if (lean_is_scalar(x_266)) {
 x_268 = lean_alloc_ctor(1, 4, 1);
} else {
 x_268 = x_266;
}
lean_ctor_set(x_268, 0, x_33);
lean_ctor_set(x_268, 1, x_34);
lean_ctor_set(x_268, 2, x_35);
lean_ctor_set(x_268, 3, x_262);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_267);
x_269 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_269, 0, x_265);
lean_ctor_set(x_269, 1, x_259);
lean_ctor_set(x_269, 2, x_260);
lean_ctor_set(x_269, 3, x_261);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_267);
x_270 = 0;
lean_ctor_set(x_1, 3, x_269);
lean_ctor_set(x_1, 2, x_264);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_268);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
return x_1;
}
}
else
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_191, 3);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
lean_free_object(x_1);
x_272 = !lean_is_exclusive(x_193);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_273 = lean_ctor_get(x_193, 3);
lean_dec(x_273);
x_274 = lean_ctor_get(x_193, 2);
lean_dec(x_274);
x_275 = lean_ctor_get(x_193, 1);
lean_dec(x_275);
x_276 = lean_ctor_get(x_193, 0);
lean_dec(x_276);
x_277 = 1;
lean_ctor_set(x_193, 3, x_191);
lean_ctor_set(x_193, 2, x_35);
lean_ctor_set(x_193, 1, x_34);
lean_ctor_set(x_193, 0, x_33);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_277);
return x_193;
}
else
{
uint8_t x_278; lean_object* x_279; 
lean_dec(x_193);
x_278 = 1;
x_279 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_279, 0, x_33);
lean_ctor_set(x_279, 1, x_34);
lean_ctor_set(x_279, 2, x_35);
lean_ctor_set(x_279, 3, x_191);
lean_ctor_set_uint8(x_279, sizeof(void*)*4, x_278);
return x_279;
}
}
else
{
uint8_t x_280; 
x_280 = lean_ctor_get_uint8(x_271, sizeof(void*)*4);
if (x_280 == 0)
{
uint8_t x_281; 
lean_free_object(x_1);
x_281 = !lean_is_exclusive(x_191);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_282 = lean_ctor_get(x_191, 3);
lean_dec(x_282);
x_283 = lean_ctor_get(x_191, 0);
lean_dec(x_283);
x_284 = !lean_is_exclusive(x_271);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_290; 
x_285 = lean_ctor_get(x_271, 0);
x_286 = lean_ctor_get(x_271, 1);
x_287 = lean_ctor_get(x_271, 2);
x_288 = lean_ctor_get(x_271, 3);
x_289 = 1;
lean_inc(x_193);
lean_ctor_set(x_271, 3, x_193);
lean_ctor_set(x_271, 2, x_35);
lean_ctor_set(x_271, 1, x_34);
lean_ctor_set(x_271, 0, x_33);
x_290 = !lean_is_exclusive(x_193);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_291 = lean_ctor_get(x_193, 3);
lean_dec(x_291);
x_292 = lean_ctor_get(x_193, 2);
lean_dec(x_292);
x_293 = lean_ctor_get(x_193, 1);
lean_dec(x_293);
x_294 = lean_ctor_get(x_193, 0);
lean_dec(x_294);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_289);
lean_ctor_set(x_193, 3, x_288);
lean_ctor_set(x_193, 2, x_287);
lean_ctor_set(x_193, 1, x_286);
lean_ctor_set(x_193, 0, x_285);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_289);
x_295 = 0;
lean_ctor_set(x_191, 3, x_193);
lean_ctor_set(x_191, 0, x_271);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_295);
return x_191;
}
else
{
lean_object* x_296; uint8_t x_297; 
lean_dec(x_193);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_289);
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_285);
lean_ctor_set(x_296, 1, x_286);
lean_ctor_set(x_296, 2, x_287);
lean_ctor_set(x_296, 3, x_288);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_289);
x_297 = 0;
lean_ctor_set(x_191, 3, x_296);
lean_ctor_set(x_191, 0, x_271);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_297);
return x_191;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_298 = lean_ctor_get(x_271, 0);
x_299 = lean_ctor_get(x_271, 1);
x_300 = lean_ctor_get(x_271, 2);
x_301 = lean_ctor_get(x_271, 3);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_271);
x_302 = 1;
lean_inc(x_193);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_33);
lean_ctor_set(x_303, 1, x_34);
lean_ctor_set(x_303, 2, x_35);
lean_ctor_set(x_303, 3, x_193);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_304 = x_193;
} else {
 lean_dec_ref(x_193);
 x_304 = lean_box(0);
}
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_302);
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 4, 1);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_298);
lean_ctor_set(x_305, 1, x_299);
lean_ctor_set(x_305, 2, x_300);
lean_ctor_set(x_305, 3, x_301);
lean_ctor_set_uint8(x_305, sizeof(void*)*4, x_302);
x_306 = 0;
lean_ctor_set(x_191, 3, x_305);
lean_ctor_set(x_191, 0, x_303);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_306);
return x_191;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; 
x_307 = lean_ctor_get(x_191, 1);
x_308 = lean_ctor_get(x_191, 2);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_191);
x_309 = lean_ctor_get(x_271, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_271, 1);
lean_inc(x_310);
x_311 = lean_ctor_get(x_271, 2);
lean_inc(x_311);
x_312 = lean_ctor_get(x_271, 3);
lean_inc(x_312);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 lean_ctor_release(x_271, 3);
 x_313 = x_271;
} else {
 lean_dec_ref(x_271);
 x_313 = lean_box(0);
}
x_314 = 1;
lean_inc(x_193);
if (lean_is_scalar(x_313)) {
 x_315 = lean_alloc_ctor(1, 4, 1);
} else {
 x_315 = x_313;
}
lean_ctor_set(x_315, 0, x_33);
lean_ctor_set(x_315, 1, x_34);
lean_ctor_set(x_315, 2, x_35);
lean_ctor_set(x_315, 3, x_193);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_316 = x_193;
} else {
 lean_dec_ref(x_193);
 x_316 = lean_box(0);
}
lean_ctor_set_uint8(x_315, sizeof(void*)*4, x_314);
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 4, 1);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_310);
lean_ctor_set(x_317, 2, x_311);
lean_ctor_set(x_317, 3, x_312);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_314);
x_318 = 0;
x_319 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_319, 0, x_315);
lean_ctor_set(x_319, 1, x_307);
lean_ctor_set(x_319, 2, x_308);
lean_ctor_set(x_319, 3, x_317);
lean_ctor_set_uint8(x_319, sizeof(void*)*4, x_318);
return x_319;
}
}
else
{
uint8_t x_320; 
x_320 = !lean_is_exclusive(x_191);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_321 = lean_ctor_get(x_191, 3);
lean_dec(x_321);
x_322 = lean_ctor_get(x_191, 0);
lean_dec(x_322);
x_323 = !lean_is_exclusive(x_193);
if (x_323 == 0)
{
uint8_t x_324; 
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_280);
x_324 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_324);
return x_1;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_325 = lean_ctor_get(x_193, 0);
x_326 = lean_ctor_get(x_193, 1);
x_327 = lean_ctor_get(x_193, 2);
x_328 = lean_ctor_get(x_193, 3);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_193);
x_329 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_329, 0, x_325);
lean_ctor_set(x_329, 1, x_326);
lean_ctor_set(x_329, 2, x_327);
lean_ctor_set(x_329, 3, x_328);
lean_ctor_set_uint8(x_329, sizeof(void*)*4, x_280);
lean_ctor_set(x_191, 0, x_329);
x_330 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_330);
return x_1;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_331 = lean_ctor_get(x_191, 1);
x_332 = lean_ctor_get(x_191, 2);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_191);
x_333 = lean_ctor_get(x_193, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_193, 1);
lean_inc(x_334);
x_335 = lean_ctor_get(x_193, 2);
lean_inc(x_335);
x_336 = lean_ctor_get(x_193, 3);
lean_inc(x_336);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_337 = x_193;
} else {
 lean_dec_ref(x_193);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_334);
lean_ctor_set(x_338, 2, x_335);
lean_ctor_set(x_338, 3, x_336);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_280);
x_339 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_331);
lean_ctor_set(x_339, 2, x_332);
lean_ctor_set(x_339, 3, x_271);
lean_ctor_set_uint8(x_339, sizeof(void*)*4, x_192);
x_340 = 1;
lean_ctor_set(x_1, 3, x_339);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_340);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_341; 
x_341 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_341);
return x_1;
}
}
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_342 = lean_ctor_get(x_1, 0);
x_343 = lean_ctor_get(x_1, 1);
x_344 = lean_ctor_get(x_1, 2);
x_345 = lean_ctor_get(x_1, 3);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_1);
x_346 = l_Lean_Name_quickCmp(x_2, x_343);
switch (x_346) {
case 0:
{
lean_object* x_347; uint8_t x_348; 
x_347 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_342, x_2, x_3);
x_348 = lean_ctor_get_uint8(x_347, sizeof(void*)*4);
if (x_348 == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_347, 0);
lean_inc(x_349);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; 
x_350 = lean_ctor_get(x_347, 3);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; 
x_351 = lean_ctor_get(x_347, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_347, 2);
lean_inc(x_352);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_353 = x_347;
} else {
 lean_dec_ref(x_347);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 4, 1);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_350);
lean_ctor_set(x_354, 1, x_351);
lean_ctor_set(x_354, 2, x_352);
lean_ctor_set(x_354, 3, x_350);
lean_ctor_set_uint8(x_354, sizeof(void*)*4, x_348);
x_355 = 1;
x_356 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_343);
lean_ctor_set(x_356, 2, x_344);
lean_ctor_set(x_356, 3, x_345);
lean_ctor_set_uint8(x_356, sizeof(void*)*4, x_355);
return x_356;
}
else
{
uint8_t x_357; 
x_357 = lean_ctor_get_uint8(x_350, sizeof(void*)*4);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_358 = lean_ctor_get(x_347, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_347, 2);
lean_inc(x_359);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_360 = x_347;
} else {
 lean_dec_ref(x_347);
 x_360 = lean_box(0);
}
x_361 = lean_ctor_get(x_350, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_350, 1);
lean_inc(x_362);
x_363 = lean_ctor_get(x_350, 2);
lean_inc(x_363);
x_364 = lean_ctor_get(x_350, 3);
lean_inc(x_364);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_365 = x_350;
} else {
 lean_dec_ref(x_350);
 x_365 = lean_box(0);
}
x_366 = 1;
if (lean_is_scalar(x_365)) {
 x_367 = lean_alloc_ctor(1, 4, 1);
} else {
 x_367 = x_365;
}
lean_ctor_set(x_367, 0, x_349);
lean_ctor_set(x_367, 1, x_358);
lean_ctor_set(x_367, 2, x_359);
lean_ctor_set(x_367, 3, x_361);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_366);
if (lean_is_scalar(x_360)) {
 x_368 = lean_alloc_ctor(1, 4, 1);
} else {
 x_368 = x_360;
}
lean_ctor_set(x_368, 0, x_364);
lean_ctor_set(x_368, 1, x_343);
lean_ctor_set(x_368, 2, x_344);
lean_ctor_set(x_368, 3, x_345);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_366);
x_369 = 0;
x_370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_362);
lean_ctor_set(x_370, 2, x_363);
lean_ctor_set(x_370, 3, x_368);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_369);
return x_370;
}
else
{
lean_object* x_371; uint8_t x_372; lean_object* x_373; 
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_371 = x_350;
} else {
 lean_dec_ref(x_350);
 x_371 = lean_box(0);
}
x_372 = 1;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_347);
lean_ctor_set(x_373, 1, x_343);
lean_ctor_set(x_373, 2, x_344);
lean_ctor_set(x_373, 3, x_345);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
return x_373;
}
}
}
else
{
uint8_t x_374; 
x_374 = lean_ctor_get_uint8(x_349, sizeof(void*)*4);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; 
x_375 = lean_ctor_get(x_347, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_347, 2);
lean_inc(x_376);
x_377 = lean_ctor_get(x_347, 3);
lean_inc(x_377);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_378 = x_347;
} else {
 lean_dec_ref(x_347);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_349, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_349, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_349, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_349, 3);
lean_inc(x_382);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_383 = x_349;
} else {
 lean_dec_ref(x_349);
 x_383 = lean_box(0);
}
x_384 = 1;
if (lean_is_scalar(x_383)) {
 x_385 = lean_alloc_ctor(1, 4, 1);
} else {
 x_385 = x_383;
}
lean_ctor_set(x_385, 0, x_379);
lean_ctor_set(x_385, 1, x_380);
lean_ctor_set(x_385, 2, x_381);
lean_ctor_set(x_385, 3, x_382);
lean_ctor_set_uint8(x_385, sizeof(void*)*4, x_384);
if (lean_is_scalar(x_378)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_378;
}
lean_ctor_set(x_386, 0, x_377);
lean_ctor_set(x_386, 1, x_343);
lean_ctor_set(x_386, 2, x_344);
lean_ctor_set(x_386, 3, x_345);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_384);
x_387 = 0;
x_388 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_375);
lean_ctor_set(x_388, 2, x_376);
lean_ctor_set(x_388, 3, x_386);
lean_ctor_set_uint8(x_388, sizeof(void*)*4, x_387);
return x_388;
}
else
{
lean_object* x_389; 
x_389 = lean_ctor_get(x_347, 3);
lean_inc(x_389);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; uint8_t x_391; lean_object* x_392; 
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_390 = x_349;
} else {
 lean_dec_ref(x_349);
 x_390 = lean_box(0);
}
x_391 = 1;
if (lean_is_scalar(x_390)) {
 x_392 = lean_alloc_ctor(1, 4, 1);
} else {
 x_392 = x_390;
}
lean_ctor_set(x_392, 0, x_347);
lean_ctor_set(x_392, 1, x_343);
lean_ctor_set(x_392, 2, x_344);
lean_ctor_set(x_392, 3, x_345);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_391);
return x_392;
}
else
{
uint8_t x_393; 
x_393 = lean_ctor_get_uint8(x_389, sizeof(void*)*4);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; 
x_394 = lean_ctor_get(x_347, 1);
lean_inc(x_394);
x_395 = lean_ctor_get(x_347, 2);
lean_inc(x_395);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_396 = x_347;
} else {
 lean_dec_ref(x_347);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_389, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_389, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_389, 2);
lean_inc(x_399);
x_400 = lean_ctor_get(x_389, 3);
lean_inc(x_400);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 lean_ctor_release(x_389, 2);
 lean_ctor_release(x_389, 3);
 x_401 = x_389;
} else {
 lean_dec_ref(x_389);
 x_401 = lean_box(0);
}
x_402 = 1;
lean_inc(x_349);
if (lean_is_scalar(x_401)) {
 x_403 = lean_alloc_ctor(1, 4, 1);
} else {
 x_403 = x_401;
}
lean_ctor_set(x_403, 0, x_349);
lean_ctor_set(x_403, 1, x_394);
lean_ctor_set(x_403, 2, x_395);
lean_ctor_set(x_403, 3, x_397);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_404 = x_349;
} else {
 lean_dec_ref(x_349);
 x_404 = lean_box(0);
}
lean_ctor_set_uint8(x_403, sizeof(void*)*4, x_402);
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(1, 4, 1);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_400);
lean_ctor_set(x_405, 1, x_343);
lean_ctor_set(x_405, 2, x_344);
lean_ctor_set(x_405, 3, x_345);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_402);
x_406 = 0;
if (lean_is_scalar(x_396)) {
 x_407 = lean_alloc_ctor(1, 4, 1);
} else {
 x_407 = x_396;
}
lean_ctor_set(x_407, 0, x_403);
lean_ctor_set(x_407, 1, x_398);
lean_ctor_set(x_407, 2, x_399);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
return x_407;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; 
x_408 = lean_ctor_get(x_347, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_347, 2);
lean_inc(x_409);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_410 = x_347;
} else {
 lean_dec_ref(x_347);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_349, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_349, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_349, 2);
lean_inc(x_413);
x_414 = lean_ctor_get(x_349, 3);
lean_inc(x_414);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_415 = x_349;
} else {
 lean_dec_ref(x_349);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(1, 4, 1);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_411);
lean_ctor_set(x_416, 1, x_412);
lean_ctor_set(x_416, 2, x_413);
lean_ctor_set(x_416, 3, x_414);
lean_ctor_set_uint8(x_416, sizeof(void*)*4, x_393);
if (lean_is_scalar(x_410)) {
 x_417 = lean_alloc_ctor(1, 4, 1);
} else {
 x_417 = x_410;
}
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_408);
lean_ctor_set(x_417, 2, x_409);
lean_ctor_set(x_417, 3, x_389);
lean_ctor_set_uint8(x_417, sizeof(void*)*4, x_348);
x_418 = 1;
x_419 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_343);
lean_ctor_set(x_419, 2, x_344);
lean_ctor_set(x_419, 3, x_345);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
return x_419;
}
}
}
}
}
else
{
uint8_t x_420; lean_object* x_421; 
x_420 = 1;
x_421 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_421, 0, x_347);
lean_ctor_set(x_421, 1, x_343);
lean_ctor_set(x_421, 2, x_344);
lean_ctor_set(x_421, 3, x_345);
lean_ctor_set_uint8(x_421, sizeof(void*)*4, x_420);
return x_421;
}
}
case 1:
{
uint8_t x_422; lean_object* x_423; 
lean_dec(x_344);
lean_dec(x_343);
x_422 = 1;
x_423 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_423, 0, x_342);
lean_ctor_set(x_423, 1, x_2);
lean_ctor_set(x_423, 2, x_3);
lean_ctor_set(x_423, 3, x_345);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
return x_423;
}
default: 
{
lean_object* x_424; uint8_t x_425; 
x_424 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_345, x_2, x_3);
x_425 = lean_ctor_get_uint8(x_424, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; 
x_426 = lean_ctor_get(x_424, 0);
lean_inc(x_426);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; 
x_427 = lean_ctor_get(x_424, 3);
lean_inc(x_427);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; 
x_428 = lean_ctor_get(x_424, 1);
lean_inc(x_428);
x_429 = lean_ctor_get(x_424, 2);
lean_inc(x_429);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_430 = x_424;
} else {
 lean_dec_ref(x_424);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 4, 1);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_427);
lean_ctor_set(x_431, 1, x_428);
lean_ctor_set(x_431, 2, x_429);
lean_ctor_set(x_431, 3, x_427);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_425);
x_432 = 1;
x_433 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_433, 0, x_342);
lean_ctor_set(x_433, 1, x_343);
lean_ctor_set(x_433, 2, x_344);
lean_ctor_set(x_433, 3, x_431);
lean_ctor_set_uint8(x_433, sizeof(void*)*4, x_432);
return x_433;
}
else
{
uint8_t x_434; 
x_434 = lean_ctor_get_uint8(x_427, sizeof(void*)*4);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; 
x_435 = lean_ctor_get(x_424, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_424, 2);
lean_inc(x_436);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_437 = x_424;
} else {
 lean_dec_ref(x_424);
 x_437 = lean_box(0);
}
x_438 = lean_ctor_get(x_427, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_427, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_427, 2);
lean_inc(x_440);
x_441 = lean_ctor_get(x_427, 3);
lean_inc(x_441);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_442 = x_427;
} else {
 lean_dec_ref(x_427);
 x_442 = lean_box(0);
}
x_443 = 1;
if (lean_is_scalar(x_442)) {
 x_444 = lean_alloc_ctor(1, 4, 1);
} else {
 x_444 = x_442;
}
lean_ctor_set(x_444, 0, x_342);
lean_ctor_set(x_444, 1, x_343);
lean_ctor_set(x_444, 2, x_344);
lean_ctor_set(x_444, 3, x_426);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_443);
if (lean_is_scalar(x_437)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_437;
}
lean_ctor_set(x_445, 0, x_438);
lean_ctor_set(x_445, 1, x_439);
lean_ctor_set(x_445, 2, x_440);
lean_ctor_set(x_445, 3, x_441);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_443);
x_446 = 0;
x_447 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_447, 0, x_444);
lean_ctor_set(x_447, 1, x_435);
lean_ctor_set(x_447, 2, x_436);
lean_ctor_set(x_447, 3, x_445);
lean_ctor_set_uint8(x_447, sizeof(void*)*4, x_446);
return x_447;
}
else
{
lean_object* x_448; uint8_t x_449; lean_object* x_450; 
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_448 = x_427;
} else {
 lean_dec_ref(x_427);
 x_448 = lean_box(0);
}
x_449 = 1;
if (lean_is_scalar(x_448)) {
 x_450 = lean_alloc_ctor(1, 4, 1);
} else {
 x_450 = x_448;
}
lean_ctor_set(x_450, 0, x_342);
lean_ctor_set(x_450, 1, x_343);
lean_ctor_set(x_450, 2, x_344);
lean_ctor_set(x_450, 3, x_424);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
return x_450;
}
}
}
else
{
uint8_t x_451; 
x_451 = lean_ctor_get_uint8(x_426, sizeof(void*)*4);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; lean_object* x_465; 
x_452 = lean_ctor_get(x_424, 1);
lean_inc(x_452);
x_453 = lean_ctor_get(x_424, 2);
lean_inc(x_453);
x_454 = lean_ctor_get(x_424, 3);
lean_inc(x_454);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_455 = x_424;
} else {
 lean_dec_ref(x_424);
 x_455 = lean_box(0);
}
x_456 = lean_ctor_get(x_426, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_426, 1);
lean_inc(x_457);
x_458 = lean_ctor_get(x_426, 2);
lean_inc(x_458);
x_459 = lean_ctor_get(x_426, 3);
lean_inc(x_459);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_460 = x_426;
} else {
 lean_dec_ref(x_426);
 x_460 = lean_box(0);
}
x_461 = 1;
if (lean_is_scalar(x_460)) {
 x_462 = lean_alloc_ctor(1, 4, 1);
} else {
 x_462 = x_460;
}
lean_ctor_set(x_462, 0, x_342);
lean_ctor_set(x_462, 1, x_343);
lean_ctor_set(x_462, 2, x_344);
lean_ctor_set(x_462, 3, x_456);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
if (lean_is_scalar(x_455)) {
 x_463 = lean_alloc_ctor(1, 4, 1);
} else {
 x_463 = x_455;
}
lean_ctor_set(x_463, 0, x_459);
lean_ctor_set(x_463, 1, x_452);
lean_ctor_set(x_463, 2, x_453);
lean_ctor_set(x_463, 3, x_454);
lean_ctor_set_uint8(x_463, sizeof(void*)*4, x_461);
x_464 = 0;
x_465 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_457);
lean_ctor_set(x_465, 2, x_458);
lean_ctor_set(x_465, 3, x_463);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_464);
return x_465;
}
else
{
lean_object* x_466; 
x_466 = lean_ctor_get(x_424, 3);
lean_inc(x_466);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; uint8_t x_468; lean_object* x_469; 
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_467 = x_426;
} else {
 lean_dec_ref(x_426);
 x_467 = lean_box(0);
}
x_468 = 1;
if (lean_is_scalar(x_467)) {
 x_469 = lean_alloc_ctor(1, 4, 1);
} else {
 x_469 = x_467;
}
lean_ctor_set(x_469, 0, x_342);
lean_ctor_set(x_469, 1, x_343);
lean_ctor_set(x_469, 2, x_344);
lean_ctor_set(x_469, 3, x_424);
lean_ctor_set_uint8(x_469, sizeof(void*)*4, x_468);
return x_469;
}
else
{
uint8_t x_470; 
x_470 = lean_ctor_get_uint8(x_466, sizeof(void*)*4);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; lean_object* x_484; 
x_471 = lean_ctor_get(x_424, 1);
lean_inc(x_471);
x_472 = lean_ctor_get(x_424, 2);
lean_inc(x_472);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_473 = x_424;
} else {
 lean_dec_ref(x_424);
 x_473 = lean_box(0);
}
x_474 = lean_ctor_get(x_466, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_466, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_466, 2);
lean_inc(x_476);
x_477 = lean_ctor_get(x_466, 3);
lean_inc(x_477);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 lean_ctor_release(x_466, 2);
 lean_ctor_release(x_466, 3);
 x_478 = x_466;
} else {
 lean_dec_ref(x_466);
 x_478 = lean_box(0);
}
x_479 = 1;
lean_inc(x_426);
if (lean_is_scalar(x_478)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_478;
}
lean_ctor_set(x_480, 0, x_342);
lean_ctor_set(x_480, 1, x_343);
lean_ctor_set(x_480, 2, x_344);
lean_ctor_set(x_480, 3, x_426);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_481 = x_426;
} else {
 lean_dec_ref(x_426);
 x_481 = lean_box(0);
}
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_479);
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(1, 4, 1);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_474);
lean_ctor_set(x_482, 1, x_475);
lean_ctor_set(x_482, 2, x_476);
lean_ctor_set(x_482, 3, x_477);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_479);
x_483 = 0;
if (lean_is_scalar(x_473)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_473;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_471);
lean_ctor_set(x_484, 2, x_472);
lean_ctor_set(x_484, 3, x_482);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_483);
return x_484;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; lean_object* x_496; 
x_485 = lean_ctor_get(x_424, 1);
lean_inc(x_485);
x_486 = lean_ctor_get(x_424, 2);
lean_inc(x_486);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_487 = x_424;
} else {
 lean_dec_ref(x_424);
 x_487 = lean_box(0);
}
x_488 = lean_ctor_get(x_426, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_426, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_426, 2);
lean_inc(x_490);
x_491 = lean_ctor_get(x_426, 3);
lean_inc(x_491);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_492 = x_426;
} else {
 lean_dec_ref(x_426);
 x_492 = lean_box(0);
}
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(1, 4, 1);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_488);
lean_ctor_set(x_493, 1, x_489);
lean_ctor_set(x_493, 2, x_490);
lean_ctor_set(x_493, 3, x_491);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_470);
if (lean_is_scalar(x_487)) {
 x_494 = lean_alloc_ctor(1, 4, 1);
} else {
 x_494 = x_487;
}
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_485);
lean_ctor_set(x_494, 2, x_486);
lean_ctor_set(x_494, 3, x_466);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_425);
x_495 = 1;
x_496 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_496, 0, x_342);
lean_ctor_set(x_496, 1, x_343);
lean_ctor_set(x_496, 2, x_344);
lean_ctor_set(x_496, 3, x_494);
lean_ctor_set_uint8(x_496, sizeof(void*)*4, x_495);
return x_496;
}
}
}
}
}
else
{
uint8_t x_497; lean_object* x_498; 
x_497 = 1;
x_498 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_498, 0, x_342);
lean_ctor_set(x_498, 1, x_343);
lean_ctor_set(x_498, 2, x_344);
lean_ctor_set(x_498, 3, x_424);
lean_ctor_set_uint8(x_498, sizeof(void*)*4, x_497);
return x_498;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__3___rarg(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__4___rarg(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_14 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_9, x_2, x_3);
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
x_17 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_12, x_2, x_3);
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
x_24 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_19, x_2, x_3);
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
x_29 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_22, x_2, x_3);
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
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_33, x_2, x_3);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*4);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_38, 3);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_38, 3);
lean_dec(x_43);
x_44 = lean_ctor_get(x_38, 0);
lean_dec(x_44);
lean_ctor_set(x_38, 0, x_41);
x_45 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_38, 1);
x_47 = lean_ctor_get(x_38, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_39);
x_49 = 1;
lean_ctor_set(x_1, 0, x_48);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_41, sizeof(void*)*4);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_38, 1);
x_53 = lean_ctor_get(x_38, 2);
x_54 = lean_ctor_get(x_38, 3);
lean_dec(x_54);
x_55 = lean_ctor_get(x_38, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_41);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_41, 0);
x_58 = lean_ctor_get(x_41, 1);
x_59 = lean_ctor_get(x_41, 2);
x_60 = lean_ctor_get(x_41, 3);
x_61 = 1;
lean_ctor_set(x_41, 3, x_57);
lean_ctor_set(x_41, 2, x_53);
lean_ctor_set(x_41, 1, x_52);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_61);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_60);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_61);
x_62 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_59);
lean_ctor_set(x_1, 1, x_58);
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_62);
return x_1;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; uint8_t x_69; 
x_63 = lean_ctor_get(x_41, 0);
x_64 = lean_ctor_get(x_41, 1);
x_65 = lean_ctor_get(x_41, 2);
x_66 = lean_ctor_get(x_41, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_41);
x_67 = 1;
x_68 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_68, 0, x_40);
lean_ctor_set(x_68, 1, x_52);
lean_ctor_set(x_68, 2, x_53);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set_uint8(x_68, sizeof(void*)*4, x_67);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_66);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_67);
x_69 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_65);
lean_ctor_set(x_1, 1, x_64);
lean_ctor_set(x_1, 0, x_68);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_70 = lean_ctor_get(x_38, 1);
x_71 = lean_ctor_get(x_38, 2);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_38);
x_72 = lean_ctor_get(x_41, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_41, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_41, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_41, 3);
lean_inc(x_75);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_76 = x_41;
} else {
 lean_dec_ref(x_41);
 x_76 = lean_box(0);
}
x_77 = 1;
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(1, 4, 1);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_40);
lean_ctor_set(x_78, 1, x_70);
lean_ctor_set(x_78, 2, x_71);
lean_ctor_set(x_78, 3, x_72);
lean_ctor_set_uint8(x_78, sizeof(void*)*4, x_77);
x_79 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_34);
lean_ctor_set(x_79, 2, x_35);
lean_ctor_set(x_79, 3, x_36);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_77);
x_80 = 0;
lean_ctor_set(x_1, 3, x_79);
lean_ctor_set(x_1, 2, x_74);
lean_ctor_set(x_1, 1, x_73);
lean_ctor_set(x_1, 0, x_78);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_80);
return x_1;
}
}
else
{
uint8_t x_81; 
lean_free_object(x_1);
x_81 = !lean_is_exclusive(x_41);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_41, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_41, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_41, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_41, 0);
lean_dec(x_85);
x_86 = 1;
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_86);
return x_41;
}
else
{
uint8_t x_87; lean_object* x_88; 
lean_dec(x_41);
x_87 = 1;
x_88 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_88, 0, x_38);
lean_ctor_set(x_88, 1, x_34);
lean_ctor_set(x_88, 2, x_35);
lean_ctor_set(x_88, 3, x_36);
lean_ctor_set_uint8(x_88, sizeof(void*)*4, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
x_89 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_38);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_91 = lean_ctor_get(x_38, 1);
x_92 = lean_ctor_get(x_38, 2);
x_93 = lean_ctor_get(x_38, 3);
x_94 = lean_ctor_get(x_38, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_40);
if (x_95 == 0)
{
uint8_t x_96; uint8_t x_97; 
x_96 = 1;
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_96);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_93);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_96);
x_97 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_92);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_40);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_97);
return x_1;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; uint8_t x_104; 
x_98 = lean_ctor_get(x_40, 0);
x_99 = lean_ctor_get(x_40, 1);
x_100 = lean_ctor_get(x_40, 2);
x_101 = lean_ctor_get(x_40, 3);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_40);
x_102 = 1;
x_103 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_99);
lean_ctor_set(x_103, 2, x_100);
lean_ctor_set(x_103, 3, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*4, x_102);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_93);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_102);
x_104 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_92);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_103);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_104);
return x_1;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_105 = lean_ctor_get(x_38, 1);
x_106 = lean_ctor_get(x_38, 2);
x_107 = lean_ctor_get(x_38, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_38);
x_108 = lean_ctor_get(x_40, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_40, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_40, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_40, 3);
lean_inc(x_111);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_112 = x_40;
} else {
 lean_dec_ref(x_40);
 x_112 = lean_box(0);
}
x_113 = 1;
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(1, 4, 1);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_109);
lean_ctor_set(x_114, 2, x_110);
lean_ctor_set(x_114, 3, x_111);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_113);
x_115 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_34);
lean_ctor_set(x_115, 2, x_35);
lean_ctor_set(x_115, 3, x_36);
lean_ctor_set_uint8(x_115, sizeof(void*)*4, x_113);
x_116 = 0;
lean_ctor_set(x_1, 3, x_115);
lean_ctor_set(x_1, 2, x_106);
lean_ctor_set(x_1, 1, x_105);
lean_ctor_set(x_1, 0, x_114);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_116);
return x_1;
}
}
else
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_38, 3);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
lean_free_object(x_1);
x_118 = !lean_is_exclusive(x_40);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_119 = lean_ctor_get(x_40, 3);
lean_dec(x_119);
x_120 = lean_ctor_get(x_40, 2);
lean_dec(x_120);
x_121 = lean_ctor_get(x_40, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_40, 0);
lean_dec(x_122);
x_123 = 1;
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_123);
return x_40;
}
else
{
uint8_t x_124; lean_object* x_125; 
lean_dec(x_40);
x_124 = 1;
x_125 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_125, 0, x_38);
lean_ctor_set(x_125, 1, x_34);
lean_ctor_set(x_125, 2, x_35);
lean_ctor_set(x_125, 3, x_36);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_124);
return x_125;
}
}
else
{
uint8_t x_126; 
x_126 = lean_ctor_get_uint8(x_117, sizeof(void*)*4);
if (x_126 == 0)
{
uint8_t x_127; 
lean_free_object(x_1);
x_127 = !lean_is_exclusive(x_38);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_38, 1);
x_129 = lean_ctor_get(x_38, 2);
x_130 = lean_ctor_get(x_38, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_38, 0);
lean_dec(x_131);
x_132 = !lean_is_exclusive(x_117);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; 
x_133 = lean_ctor_get(x_117, 0);
x_134 = lean_ctor_get(x_117, 1);
x_135 = lean_ctor_get(x_117, 2);
x_136 = lean_ctor_get(x_117, 3);
x_137 = 1;
lean_inc(x_40);
lean_ctor_set(x_117, 3, x_133);
lean_ctor_set(x_117, 2, x_129);
lean_ctor_set(x_117, 1, x_128);
lean_ctor_set(x_117, 0, x_40);
x_138 = !lean_is_exclusive(x_40);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_139 = lean_ctor_get(x_40, 3);
lean_dec(x_139);
x_140 = lean_ctor_get(x_40, 2);
lean_dec(x_140);
x_141 = lean_ctor_get(x_40, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_40, 0);
lean_dec(x_142);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_137);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 0, x_136);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_137);
x_143 = 0;
lean_ctor_set(x_38, 3, x_40);
lean_ctor_set(x_38, 2, x_135);
lean_ctor_set(x_38, 1, x_134);
lean_ctor_set(x_38, 0, x_117);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_143);
return x_38;
}
else
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_40);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_137);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_136);
lean_ctor_set(x_144, 1, x_34);
lean_ctor_set(x_144, 2, x_35);
lean_ctor_set(x_144, 3, x_36);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_137);
x_145 = 0;
lean_ctor_set(x_38, 3, x_144);
lean_ctor_set(x_38, 2, x_135);
lean_ctor_set(x_38, 1, x_134);
lean_ctor_set(x_38, 0, x_117);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_145);
return x_38;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_146 = lean_ctor_get(x_117, 0);
x_147 = lean_ctor_get(x_117, 1);
x_148 = lean_ctor_get(x_117, 2);
x_149 = lean_ctor_get(x_117, 3);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_117);
x_150 = 1;
lean_inc(x_40);
x_151 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_151, 0, x_40);
lean_ctor_set(x_151, 1, x_128);
lean_ctor_set(x_151, 2, x_129);
lean_ctor_set(x_151, 3, x_146);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_152 = x_40;
} else {
 lean_dec_ref(x_40);
 x_152 = lean_box(0);
}
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_150);
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 4, 1);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_34);
lean_ctor_set(x_153, 2, x_35);
lean_ctor_set(x_153, 3, x_36);
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_150);
x_154 = 0;
lean_ctor_set(x_38, 3, x_153);
lean_ctor_set(x_38, 2, x_148);
lean_ctor_set(x_38, 1, x_147);
lean_ctor_set(x_38, 0, x_151);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_154);
return x_38;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; 
x_155 = lean_ctor_get(x_38, 1);
x_156 = lean_ctor_get(x_38, 2);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_38);
x_157 = lean_ctor_get(x_117, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_117, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_117, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_117, 3);
lean_inc(x_160);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 x_161 = x_117;
} else {
 lean_dec_ref(x_117);
 x_161 = lean_box(0);
}
x_162 = 1;
lean_inc(x_40);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(1, 4, 1);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_40);
lean_ctor_set(x_163, 1, x_155);
lean_ctor_set(x_163, 2, x_156);
lean_ctor_set(x_163, 3, x_157);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_164 = x_40;
} else {
 lean_dec_ref(x_40);
 x_164 = lean_box(0);
}
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_162);
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 4, 1);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_160);
lean_ctor_set(x_165, 1, x_34);
lean_ctor_set(x_165, 2, x_35);
lean_ctor_set(x_165, 3, x_36);
lean_ctor_set_uint8(x_165, sizeof(void*)*4, x_162);
x_166 = 0;
x_167 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_167, 0, x_163);
lean_ctor_set(x_167, 1, x_158);
lean_ctor_set(x_167, 2, x_159);
lean_ctor_set(x_167, 3, x_165);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_166);
return x_167;
}
}
else
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_38);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_ctor_get(x_38, 3);
lean_dec(x_169);
x_170 = lean_ctor_get(x_38, 0);
lean_dec(x_170);
x_171 = !lean_is_exclusive(x_40);
if (x_171 == 0)
{
uint8_t x_172; 
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_126);
x_172 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_172);
return x_1;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_173 = lean_ctor_get(x_40, 0);
x_174 = lean_ctor_get(x_40, 1);
x_175 = lean_ctor_get(x_40, 2);
x_176 = lean_ctor_get(x_40, 3);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_40);
x_177 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_174);
lean_ctor_set(x_177, 2, x_175);
lean_ctor_set(x_177, 3, x_176);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_126);
lean_ctor_set(x_38, 0, x_177);
x_178 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_178);
return x_1;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_179 = lean_ctor_get(x_38, 1);
x_180 = lean_ctor_get(x_38, 2);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_38);
x_181 = lean_ctor_get(x_40, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_40, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_40, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_40, 3);
lean_inc(x_184);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_185 = x_40;
} else {
 lean_dec_ref(x_40);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 4, 1);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_181);
lean_ctor_set(x_186, 1, x_182);
lean_ctor_set(x_186, 2, x_183);
lean_ctor_set(x_186, 3, x_184);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_126);
x_187 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_179);
lean_ctor_set(x_187, 2, x_180);
lean_ctor_set(x_187, 3, x_117);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_39);
x_188 = 1;
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_189; 
x_189 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
case 1:
{
uint8_t x_190; 
lean_dec(x_35);
lean_dec(x_34);
x_190 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_190);
return x_1;
}
default: 
{
lean_object* x_191; uint8_t x_192; 
x_191 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_36, x_2, x_3);
x_192 = lean_ctor_get_uint8(x_191, sizeof(void*)*4);
if (x_192 == 0)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_191, 3);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_191);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_196 = lean_ctor_get(x_191, 3);
lean_dec(x_196);
x_197 = lean_ctor_get(x_191, 0);
lean_dec(x_197);
lean_ctor_set(x_191, 0, x_194);
x_198 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_198);
return x_1;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_199 = lean_ctor_get(x_191, 1);
x_200 = lean_ctor_get(x_191, 2);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_191);
x_201 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_201, 0, x_194);
lean_ctor_set(x_201, 1, x_199);
lean_ctor_set(x_201, 2, x_200);
lean_ctor_set(x_201, 3, x_194);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_192);
x_202 = 1;
lean_ctor_set(x_1, 3, x_201);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
}
}
else
{
uint8_t x_203; 
x_203 = lean_ctor_get_uint8(x_194, sizeof(void*)*4);
if (x_203 == 0)
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_191);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_191, 1);
x_206 = lean_ctor_get(x_191, 2);
x_207 = lean_ctor_get(x_191, 3);
lean_dec(x_207);
x_208 = lean_ctor_get(x_191, 0);
lean_dec(x_208);
x_209 = !lean_is_exclusive(x_194);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; 
x_210 = lean_ctor_get(x_194, 0);
x_211 = lean_ctor_get(x_194, 1);
x_212 = lean_ctor_get(x_194, 2);
x_213 = lean_ctor_get(x_194, 3);
x_214 = 1;
lean_ctor_set(x_194, 3, x_193);
lean_ctor_set(x_194, 2, x_35);
lean_ctor_set(x_194, 1, x_34);
lean_ctor_set(x_194, 0, x_33);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_214);
lean_ctor_set(x_191, 3, x_213);
lean_ctor_set(x_191, 2, x_212);
lean_ctor_set(x_191, 1, x_211);
lean_ctor_set(x_191, 0, x_210);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_214);
x_215 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_215);
return x_1;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; uint8_t x_222; 
x_216 = lean_ctor_get(x_194, 0);
x_217 = lean_ctor_get(x_194, 1);
x_218 = lean_ctor_get(x_194, 2);
x_219 = lean_ctor_get(x_194, 3);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_194);
x_220 = 1;
x_221 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_221, 0, x_33);
lean_ctor_set(x_221, 1, x_34);
lean_ctor_set(x_221, 2, x_35);
lean_ctor_set(x_221, 3, x_193);
lean_ctor_set_uint8(x_221, sizeof(void*)*4, x_220);
lean_ctor_set(x_191, 3, x_219);
lean_ctor_set(x_191, 2, x_218);
lean_ctor_set(x_191, 1, x_217);
lean_ctor_set(x_191, 0, x_216);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_220);
x_222 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_221);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_222);
return x_1;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_223 = lean_ctor_get(x_191, 1);
x_224 = lean_ctor_get(x_191, 2);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_191);
x_225 = lean_ctor_get(x_194, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_194, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_194, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_194, 3);
lean_inc(x_228);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_229 = x_194;
} else {
 lean_dec_ref(x_194);
 x_229 = lean_box(0);
}
x_230 = 1;
if (lean_is_scalar(x_229)) {
 x_231 = lean_alloc_ctor(1, 4, 1);
} else {
 x_231 = x_229;
}
lean_ctor_set(x_231, 0, x_33);
lean_ctor_set(x_231, 1, x_34);
lean_ctor_set(x_231, 2, x_35);
lean_ctor_set(x_231, 3, x_193);
lean_ctor_set_uint8(x_231, sizeof(void*)*4, x_230);
x_232 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_232, 0, x_225);
lean_ctor_set(x_232, 1, x_226);
lean_ctor_set(x_232, 2, x_227);
lean_ctor_set(x_232, 3, x_228);
lean_ctor_set_uint8(x_232, sizeof(void*)*4, x_230);
x_233 = 0;
lean_ctor_set(x_1, 3, x_232);
lean_ctor_set(x_1, 2, x_224);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_1, 0, x_231);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
}
else
{
uint8_t x_234; 
lean_free_object(x_1);
x_234 = !lean_is_exclusive(x_194);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_235 = lean_ctor_get(x_194, 3);
lean_dec(x_235);
x_236 = lean_ctor_get(x_194, 2);
lean_dec(x_236);
x_237 = lean_ctor_get(x_194, 1);
lean_dec(x_237);
x_238 = lean_ctor_get(x_194, 0);
lean_dec(x_238);
x_239 = 1;
lean_ctor_set(x_194, 3, x_191);
lean_ctor_set(x_194, 2, x_35);
lean_ctor_set(x_194, 1, x_34);
lean_ctor_set(x_194, 0, x_33);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_239);
return x_194;
}
else
{
uint8_t x_240; lean_object* x_241; 
lean_dec(x_194);
x_240 = 1;
x_241 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_241, 0, x_33);
lean_ctor_set(x_241, 1, x_34);
lean_ctor_set(x_241, 2, x_35);
lean_ctor_set(x_241, 3, x_191);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_240);
return x_241;
}
}
}
}
else
{
uint8_t x_242; 
x_242 = lean_ctor_get_uint8(x_193, sizeof(void*)*4);
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = !lean_is_exclusive(x_191);
if (x_243 == 0)
{
lean_object* x_244; uint8_t x_245; 
x_244 = lean_ctor_get(x_191, 0);
lean_dec(x_244);
x_245 = !lean_is_exclusive(x_193);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_251; 
x_246 = lean_ctor_get(x_193, 0);
x_247 = lean_ctor_get(x_193, 1);
x_248 = lean_ctor_get(x_193, 2);
x_249 = lean_ctor_get(x_193, 3);
x_250 = 1;
lean_ctor_set(x_193, 3, x_246);
lean_ctor_set(x_193, 2, x_35);
lean_ctor_set(x_193, 1, x_34);
lean_ctor_set(x_193, 0, x_33);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_250);
lean_ctor_set(x_191, 0, x_249);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_250);
x_251 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_248);
lean_ctor_set(x_1, 1, x_247);
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_251);
return x_1;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; uint8_t x_258; 
x_252 = lean_ctor_get(x_193, 0);
x_253 = lean_ctor_get(x_193, 1);
x_254 = lean_ctor_get(x_193, 2);
x_255 = lean_ctor_get(x_193, 3);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_193);
x_256 = 1;
x_257 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_257, 0, x_33);
lean_ctor_set(x_257, 1, x_34);
lean_ctor_set(x_257, 2, x_35);
lean_ctor_set(x_257, 3, x_252);
lean_ctor_set_uint8(x_257, sizeof(void*)*4, x_256);
lean_ctor_set(x_191, 0, x_255);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_256);
x_258 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_254);
lean_ctor_set(x_1, 1, x_253);
lean_ctor_set(x_1, 0, x_257);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_258);
return x_1;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_259 = lean_ctor_get(x_191, 1);
x_260 = lean_ctor_get(x_191, 2);
x_261 = lean_ctor_get(x_191, 3);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_191);
x_262 = lean_ctor_get(x_193, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_193, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_193, 2);
lean_inc(x_264);
x_265 = lean_ctor_get(x_193, 3);
lean_inc(x_265);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_266 = x_193;
} else {
 lean_dec_ref(x_193);
 x_266 = lean_box(0);
}
x_267 = 1;
if (lean_is_scalar(x_266)) {
 x_268 = lean_alloc_ctor(1, 4, 1);
} else {
 x_268 = x_266;
}
lean_ctor_set(x_268, 0, x_33);
lean_ctor_set(x_268, 1, x_34);
lean_ctor_set(x_268, 2, x_35);
lean_ctor_set(x_268, 3, x_262);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_267);
x_269 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_269, 0, x_265);
lean_ctor_set(x_269, 1, x_259);
lean_ctor_set(x_269, 2, x_260);
lean_ctor_set(x_269, 3, x_261);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_267);
x_270 = 0;
lean_ctor_set(x_1, 3, x_269);
lean_ctor_set(x_1, 2, x_264);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_268);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
return x_1;
}
}
else
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_191, 3);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
lean_free_object(x_1);
x_272 = !lean_is_exclusive(x_193);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_273 = lean_ctor_get(x_193, 3);
lean_dec(x_273);
x_274 = lean_ctor_get(x_193, 2);
lean_dec(x_274);
x_275 = lean_ctor_get(x_193, 1);
lean_dec(x_275);
x_276 = lean_ctor_get(x_193, 0);
lean_dec(x_276);
x_277 = 1;
lean_ctor_set(x_193, 3, x_191);
lean_ctor_set(x_193, 2, x_35);
lean_ctor_set(x_193, 1, x_34);
lean_ctor_set(x_193, 0, x_33);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_277);
return x_193;
}
else
{
uint8_t x_278; lean_object* x_279; 
lean_dec(x_193);
x_278 = 1;
x_279 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_279, 0, x_33);
lean_ctor_set(x_279, 1, x_34);
lean_ctor_set(x_279, 2, x_35);
lean_ctor_set(x_279, 3, x_191);
lean_ctor_set_uint8(x_279, sizeof(void*)*4, x_278);
return x_279;
}
}
else
{
uint8_t x_280; 
x_280 = lean_ctor_get_uint8(x_271, sizeof(void*)*4);
if (x_280 == 0)
{
uint8_t x_281; 
lean_free_object(x_1);
x_281 = !lean_is_exclusive(x_191);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_282 = lean_ctor_get(x_191, 3);
lean_dec(x_282);
x_283 = lean_ctor_get(x_191, 0);
lean_dec(x_283);
x_284 = !lean_is_exclusive(x_271);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_290; 
x_285 = lean_ctor_get(x_271, 0);
x_286 = lean_ctor_get(x_271, 1);
x_287 = lean_ctor_get(x_271, 2);
x_288 = lean_ctor_get(x_271, 3);
x_289 = 1;
lean_inc(x_193);
lean_ctor_set(x_271, 3, x_193);
lean_ctor_set(x_271, 2, x_35);
lean_ctor_set(x_271, 1, x_34);
lean_ctor_set(x_271, 0, x_33);
x_290 = !lean_is_exclusive(x_193);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_291 = lean_ctor_get(x_193, 3);
lean_dec(x_291);
x_292 = lean_ctor_get(x_193, 2);
lean_dec(x_292);
x_293 = lean_ctor_get(x_193, 1);
lean_dec(x_293);
x_294 = lean_ctor_get(x_193, 0);
lean_dec(x_294);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_289);
lean_ctor_set(x_193, 3, x_288);
lean_ctor_set(x_193, 2, x_287);
lean_ctor_set(x_193, 1, x_286);
lean_ctor_set(x_193, 0, x_285);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_289);
x_295 = 0;
lean_ctor_set(x_191, 3, x_193);
lean_ctor_set(x_191, 0, x_271);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_295);
return x_191;
}
else
{
lean_object* x_296; uint8_t x_297; 
lean_dec(x_193);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_289);
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_285);
lean_ctor_set(x_296, 1, x_286);
lean_ctor_set(x_296, 2, x_287);
lean_ctor_set(x_296, 3, x_288);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_289);
x_297 = 0;
lean_ctor_set(x_191, 3, x_296);
lean_ctor_set(x_191, 0, x_271);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_297);
return x_191;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_298 = lean_ctor_get(x_271, 0);
x_299 = lean_ctor_get(x_271, 1);
x_300 = lean_ctor_get(x_271, 2);
x_301 = lean_ctor_get(x_271, 3);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_271);
x_302 = 1;
lean_inc(x_193);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_33);
lean_ctor_set(x_303, 1, x_34);
lean_ctor_set(x_303, 2, x_35);
lean_ctor_set(x_303, 3, x_193);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_304 = x_193;
} else {
 lean_dec_ref(x_193);
 x_304 = lean_box(0);
}
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_302);
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 4, 1);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_298);
lean_ctor_set(x_305, 1, x_299);
lean_ctor_set(x_305, 2, x_300);
lean_ctor_set(x_305, 3, x_301);
lean_ctor_set_uint8(x_305, sizeof(void*)*4, x_302);
x_306 = 0;
lean_ctor_set(x_191, 3, x_305);
lean_ctor_set(x_191, 0, x_303);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_306);
return x_191;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; 
x_307 = lean_ctor_get(x_191, 1);
x_308 = lean_ctor_get(x_191, 2);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_191);
x_309 = lean_ctor_get(x_271, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_271, 1);
lean_inc(x_310);
x_311 = lean_ctor_get(x_271, 2);
lean_inc(x_311);
x_312 = lean_ctor_get(x_271, 3);
lean_inc(x_312);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 lean_ctor_release(x_271, 3);
 x_313 = x_271;
} else {
 lean_dec_ref(x_271);
 x_313 = lean_box(0);
}
x_314 = 1;
lean_inc(x_193);
if (lean_is_scalar(x_313)) {
 x_315 = lean_alloc_ctor(1, 4, 1);
} else {
 x_315 = x_313;
}
lean_ctor_set(x_315, 0, x_33);
lean_ctor_set(x_315, 1, x_34);
lean_ctor_set(x_315, 2, x_35);
lean_ctor_set(x_315, 3, x_193);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_316 = x_193;
} else {
 lean_dec_ref(x_193);
 x_316 = lean_box(0);
}
lean_ctor_set_uint8(x_315, sizeof(void*)*4, x_314);
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 4, 1);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_310);
lean_ctor_set(x_317, 2, x_311);
lean_ctor_set(x_317, 3, x_312);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_314);
x_318 = 0;
x_319 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_319, 0, x_315);
lean_ctor_set(x_319, 1, x_307);
lean_ctor_set(x_319, 2, x_308);
lean_ctor_set(x_319, 3, x_317);
lean_ctor_set_uint8(x_319, sizeof(void*)*4, x_318);
return x_319;
}
}
else
{
uint8_t x_320; 
x_320 = !lean_is_exclusive(x_191);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_321 = lean_ctor_get(x_191, 3);
lean_dec(x_321);
x_322 = lean_ctor_get(x_191, 0);
lean_dec(x_322);
x_323 = !lean_is_exclusive(x_193);
if (x_323 == 0)
{
uint8_t x_324; 
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_280);
x_324 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_324);
return x_1;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_325 = lean_ctor_get(x_193, 0);
x_326 = lean_ctor_get(x_193, 1);
x_327 = lean_ctor_get(x_193, 2);
x_328 = lean_ctor_get(x_193, 3);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_193);
x_329 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_329, 0, x_325);
lean_ctor_set(x_329, 1, x_326);
lean_ctor_set(x_329, 2, x_327);
lean_ctor_set(x_329, 3, x_328);
lean_ctor_set_uint8(x_329, sizeof(void*)*4, x_280);
lean_ctor_set(x_191, 0, x_329);
x_330 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_330);
return x_1;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_331 = lean_ctor_get(x_191, 1);
x_332 = lean_ctor_get(x_191, 2);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_191);
x_333 = lean_ctor_get(x_193, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_193, 1);
lean_inc(x_334);
x_335 = lean_ctor_get(x_193, 2);
lean_inc(x_335);
x_336 = lean_ctor_get(x_193, 3);
lean_inc(x_336);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_337 = x_193;
} else {
 lean_dec_ref(x_193);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_334);
lean_ctor_set(x_338, 2, x_335);
lean_ctor_set(x_338, 3, x_336);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_280);
x_339 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_331);
lean_ctor_set(x_339, 2, x_332);
lean_ctor_set(x_339, 3, x_271);
lean_ctor_set_uint8(x_339, sizeof(void*)*4, x_192);
x_340 = 1;
lean_ctor_set(x_1, 3, x_339);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_340);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_341; 
x_341 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_341);
return x_1;
}
}
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_342 = lean_ctor_get(x_1, 0);
x_343 = lean_ctor_get(x_1, 1);
x_344 = lean_ctor_get(x_1, 2);
x_345 = lean_ctor_get(x_1, 3);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_1);
x_346 = l_Lean_Name_quickCmp(x_2, x_343);
switch (x_346) {
case 0:
{
lean_object* x_347; uint8_t x_348; 
x_347 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_342, x_2, x_3);
x_348 = lean_ctor_get_uint8(x_347, sizeof(void*)*4);
if (x_348 == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_347, 0);
lean_inc(x_349);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; 
x_350 = lean_ctor_get(x_347, 3);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; 
x_351 = lean_ctor_get(x_347, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_347, 2);
lean_inc(x_352);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_353 = x_347;
} else {
 lean_dec_ref(x_347);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 4, 1);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_350);
lean_ctor_set(x_354, 1, x_351);
lean_ctor_set(x_354, 2, x_352);
lean_ctor_set(x_354, 3, x_350);
lean_ctor_set_uint8(x_354, sizeof(void*)*4, x_348);
x_355 = 1;
x_356 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_343);
lean_ctor_set(x_356, 2, x_344);
lean_ctor_set(x_356, 3, x_345);
lean_ctor_set_uint8(x_356, sizeof(void*)*4, x_355);
return x_356;
}
else
{
uint8_t x_357; 
x_357 = lean_ctor_get_uint8(x_350, sizeof(void*)*4);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_358 = lean_ctor_get(x_347, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_347, 2);
lean_inc(x_359);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_360 = x_347;
} else {
 lean_dec_ref(x_347);
 x_360 = lean_box(0);
}
x_361 = lean_ctor_get(x_350, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_350, 1);
lean_inc(x_362);
x_363 = lean_ctor_get(x_350, 2);
lean_inc(x_363);
x_364 = lean_ctor_get(x_350, 3);
lean_inc(x_364);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_365 = x_350;
} else {
 lean_dec_ref(x_350);
 x_365 = lean_box(0);
}
x_366 = 1;
if (lean_is_scalar(x_365)) {
 x_367 = lean_alloc_ctor(1, 4, 1);
} else {
 x_367 = x_365;
}
lean_ctor_set(x_367, 0, x_349);
lean_ctor_set(x_367, 1, x_358);
lean_ctor_set(x_367, 2, x_359);
lean_ctor_set(x_367, 3, x_361);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_366);
if (lean_is_scalar(x_360)) {
 x_368 = lean_alloc_ctor(1, 4, 1);
} else {
 x_368 = x_360;
}
lean_ctor_set(x_368, 0, x_364);
lean_ctor_set(x_368, 1, x_343);
lean_ctor_set(x_368, 2, x_344);
lean_ctor_set(x_368, 3, x_345);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_366);
x_369 = 0;
x_370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_362);
lean_ctor_set(x_370, 2, x_363);
lean_ctor_set(x_370, 3, x_368);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_369);
return x_370;
}
else
{
lean_object* x_371; uint8_t x_372; lean_object* x_373; 
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_371 = x_350;
} else {
 lean_dec_ref(x_350);
 x_371 = lean_box(0);
}
x_372 = 1;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_347);
lean_ctor_set(x_373, 1, x_343);
lean_ctor_set(x_373, 2, x_344);
lean_ctor_set(x_373, 3, x_345);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
return x_373;
}
}
}
else
{
uint8_t x_374; 
x_374 = lean_ctor_get_uint8(x_349, sizeof(void*)*4);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; 
x_375 = lean_ctor_get(x_347, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_347, 2);
lean_inc(x_376);
x_377 = lean_ctor_get(x_347, 3);
lean_inc(x_377);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_378 = x_347;
} else {
 lean_dec_ref(x_347);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_349, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_349, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_349, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_349, 3);
lean_inc(x_382);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_383 = x_349;
} else {
 lean_dec_ref(x_349);
 x_383 = lean_box(0);
}
x_384 = 1;
if (lean_is_scalar(x_383)) {
 x_385 = lean_alloc_ctor(1, 4, 1);
} else {
 x_385 = x_383;
}
lean_ctor_set(x_385, 0, x_379);
lean_ctor_set(x_385, 1, x_380);
lean_ctor_set(x_385, 2, x_381);
lean_ctor_set(x_385, 3, x_382);
lean_ctor_set_uint8(x_385, sizeof(void*)*4, x_384);
if (lean_is_scalar(x_378)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_378;
}
lean_ctor_set(x_386, 0, x_377);
lean_ctor_set(x_386, 1, x_343);
lean_ctor_set(x_386, 2, x_344);
lean_ctor_set(x_386, 3, x_345);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_384);
x_387 = 0;
x_388 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_375);
lean_ctor_set(x_388, 2, x_376);
lean_ctor_set(x_388, 3, x_386);
lean_ctor_set_uint8(x_388, sizeof(void*)*4, x_387);
return x_388;
}
else
{
lean_object* x_389; 
x_389 = lean_ctor_get(x_347, 3);
lean_inc(x_389);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; uint8_t x_391; lean_object* x_392; 
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_390 = x_349;
} else {
 lean_dec_ref(x_349);
 x_390 = lean_box(0);
}
x_391 = 1;
if (lean_is_scalar(x_390)) {
 x_392 = lean_alloc_ctor(1, 4, 1);
} else {
 x_392 = x_390;
}
lean_ctor_set(x_392, 0, x_347);
lean_ctor_set(x_392, 1, x_343);
lean_ctor_set(x_392, 2, x_344);
lean_ctor_set(x_392, 3, x_345);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_391);
return x_392;
}
else
{
uint8_t x_393; 
x_393 = lean_ctor_get_uint8(x_389, sizeof(void*)*4);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; 
x_394 = lean_ctor_get(x_347, 1);
lean_inc(x_394);
x_395 = lean_ctor_get(x_347, 2);
lean_inc(x_395);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_396 = x_347;
} else {
 lean_dec_ref(x_347);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_389, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_389, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_389, 2);
lean_inc(x_399);
x_400 = lean_ctor_get(x_389, 3);
lean_inc(x_400);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 lean_ctor_release(x_389, 2);
 lean_ctor_release(x_389, 3);
 x_401 = x_389;
} else {
 lean_dec_ref(x_389);
 x_401 = lean_box(0);
}
x_402 = 1;
lean_inc(x_349);
if (lean_is_scalar(x_401)) {
 x_403 = lean_alloc_ctor(1, 4, 1);
} else {
 x_403 = x_401;
}
lean_ctor_set(x_403, 0, x_349);
lean_ctor_set(x_403, 1, x_394);
lean_ctor_set(x_403, 2, x_395);
lean_ctor_set(x_403, 3, x_397);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_404 = x_349;
} else {
 lean_dec_ref(x_349);
 x_404 = lean_box(0);
}
lean_ctor_set_uint8(x_403, sizeof(void*)*4, x_402);
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(1, 4, 1);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_400);
lean_ctor_set(x_405, 1, x_343);
lean_ctor_set(x_405, 2, x_344);
lean_ctor_set(x_405, 3, x_345);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_402);
x_406 = 0;
if (lean_is_scalar(x_396)) {
 x_407 = lean_alloc_ctor(1, 4, 1);
} else {
 x_407 = x_396;
}
lean_ctor_set(x_407, 0, x_403);
lean_ctor_set(x_407, 1, x_398);
lean_ctor_set(x_407, 2, x_399);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
return x_407;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; 
x_408 = lean_ctor_get(x_347, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_347, 2);
lean_inc(x_409);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_410 = x_347;
} else {
 lean_dec_ref(x_347);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_349, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_349, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_349, 2);
lean_inc(x_413);
x_414 = lean_ctor_get(x_349, 3);
lean_inc(x_414);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_415 = x_349;
} else {
 lean_dec_ref(x_349);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(1, 4, 1);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_411);
lean_ctor_set(x_416, 1, x_412);
lean_ctor_set(x_416, 2, x_413);
lean_ctor_set(x_416, 3, x_414);
lean_ctor_set_uint8(x_416, sizeof(void*)*4, x_393);
if (lean_is_scalar(x_410)) {
 x_417 = lean_alloc_ctor(1, 4, 1);
} else {
 x_417 = x_410;
}
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_408);
lean_ctor_set(x_417, 2, x_409);
lean_ctor_set(x_417, 3, x_389);
lean_ctor_set_uint8(x_417, sizeof(void*)*4, x_348);
x_418 = 1;
x_419 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_343);
lean_ctor_set(x_419, 2, x_344);
lean_ctor_set(x_419, 3, x_345);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
return x_419;
}
}
}
}
}
else
{
uint8_t x_420; lean_object* x_421; 
x_420 = 1;
x_421 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_421, 0, x_347);
lean_ctor_set(x_421, 1, x_343);
lean_ctor_set(x_421, 2, x_344);
lean_ctor_set(x_421, 3, x_345);
lean_ctor_set_uint8(x_421, sizeof(void*)*4, x_420);
return x_421;
}
}
case 1:
{
uint8_t x_422; lean_object* x_423; 
lean_dec(x_344);
lean_dec(x_343);
x_422 = 1;
x_423 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_423, 0, x_342);
lean_ctor_set(x_423, 1, x_2);
lean_ctor_set(x_423, 2, x_3);
lean_ctor_set(x_423, 3, x_345);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
return x_423;
}
default: 
{
lean_object* x_424; uint8_t x_425; 
x_424 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_345, x_2, x_3);
x_425 = lean_ctor_get_uint8(x_424, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; 
x_426 = lean_ctor_get(x_424, 0);
lean_inc(x_426);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; 
x_427 = lean_ctor_get(x_424, 3);
lean_inc(x_427);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; 
x_428 = lean_ctor_get(x_424, 1);
lean_inc(x_428);
x_429 = lean_ctor_get(x_424, 2);
lean_inc(x_429);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_430 = x_424;
} else {
 lean_dec_ref(x_424);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 4, 1);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_427);
lean_ctor_set(x_431, 1, x_428);
lean_ctor_set(x_431, 2, x_429);
lean_ctor_set(x_431, 3, x_427);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_425);
x_432 = 1;
x_433 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_433, 0, x_342);
lean_ctor_set(x_433, 1, x_343);
lean_ctor_set(x_433, 2, x_344);
lean_ctor_set(x_433, 3, x_431);
lean_ctor_set_uint8(x_433, sizeof(void*)*4, x_432);
return x_433;
}
else
{
uint8_t x_434; 
x_434 = lean_ctor_get_uint8(x_427, sizeof(void*)*4);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; 
x_435 = lean_ctor_get(x_424, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_424, 2);
lean_inc(x_436);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_437 = x_424;
} else {
 lean_dec_ref(x_424);
 x_437 = lean_box(0);
}
x_438 = lean_ctor_get(x_427, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_427, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_427, 2);
lean_inc(x_440);
x_441 = lean_ctor_get(x_427, 3);
lean_inc(x_441);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_442 = x_427;
} else {
 lean_dec_ref(x_427);
 x_442 = lean_box(0);
}
x_443 = 1;
if (lean_is_scalar(x_442)) {
 x_444 = lean_alloc_ctor(1, 4, 1);
} else {
 x_444 = x_442;
}
lean_ctor_set(x_444, 0, x_342);
lean_ctor_set(x_444, 1, x_343);
lean_ctor_set(x_444, 2, x_344);
lean_ctor_set(x_444, 3, x_426);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_443);
if (lean_is_scalar(x_437)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_437;
}
lean_ctor_set(x_445, 0, x_438);
lean_ctor_set(x_445, 1, x_439);
lean_ctor_set(x_445, 2, x_440);
lean_ctor_set(x_445, 3, x_441);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_443);
x_446 = 0;
x_447 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_447, 0, x_444);
lean_ctor_set(x_447, 1, x_435);
lean_ctor_set(x_447, 2, x_436);
lean_ctor_set(x_447, 3, x_445);
lean_ctor_set_uint8(x_447, sizeof(void*)*4, x_446);
return x_447;
}
else
{
lean_object* x_448; uint8_t x_449; lean_object* x_450; 
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_448 = x_427;
} else {
 lean_dec_ref(x_427);
 x_448 = lean_box(0);
}
x_449 = 1;
if (lean_is_scalar(x_448)) {
 x_450 = lean_alloc_ctor(1, 4, 1);
} else {
 x_450 = x_448;
}
lean_ctor_set(x_450, 0, x_342);
lean_ctor_set(x_450, 1, x_343);
lean_ctor_set(x_450, 2, x_344);
lean_ctor_set(x_450, 3, x_424);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
return x_450;
}
}
}
else
{
uint8_t x_451; 
x_451 = lean_ctor_get_uint8(x_426, sizeof(void*)*4);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; lean_object* x_465; 
x_452 = lean_ctor_get(x_424, 1);
lean_inc(x_452);
x_453 = lean_ctor_get(x_424, 2);
lean_inc(x_453);
x_454 = lean_ctor_get(x_424, 3);
lean_inc(x_454);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_455 = x_424;
} else {
 lean_dec_ref(x_424);
 x_455 = lean_box(0);
}
x_456 = lean_ctor_get(x_426, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_426, 1);
lean_inc(x_457);
x_458 = lean_ctor_get(x_426, 2);
lean_inc(x_458);
x_459 = lean_ctor_get(x_426, 3);
lean_inc(x_459);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_460 = x_426;
} else {
 lean_dec_ref(x_426);
 x_460 = lean_box(0);
}
x_461 = 1;
if (lean_is_scalar(x_460)) {
 x_462 = lean_alloc_ctor(1, 4, 1);
} else {
 x_462 = x_460;
}
lean_ctor_set(x_462, 0, x_342);
lean_ctor_set(x_462, 1, x_343);
lean_ctor_set(x_462, 2, x_344);
lean_ctor_set(x_462, 3, x_456);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
if (lean_is_scalar(x_455)) {
 x_463 = lean_alloc_ctor(1, 4, 1);
} else {
 x_463 = x_455;
}
lean_ctor_set(x_463, 0, x_459);
lean_ctor_set(x_463, 1, x_452);
lean_ctor_set(x_463, 2, x_453);
lean_ctor_set(x_463, 3, x_454);
lean_ctor_set_uint8(x_463, sizeof(void*)*4, x_461);
x_464 = 0;
x_465 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_457);
lean_ctor_set(x_465, 2, x_458);
lean_ctor_set(x_465, 3, x_463);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_464);
return x_465;
}
else
{
lean_object* x_466; 
x_466 = lean_ctor_get(x_424, 3);
lean_inc(x_466);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; uint8_t x_468; lean_object* x_469; 
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_467 = x_426;
} else {
 lean_dec_ref(x_426);
 x_467 = lean_box(0);
}
x_468 = 1;
if (lean_is_scalar(x_467)) {
 x_469 = lean_alloc_ctor(1, 4, 1);
} else {
 x_469 = x_467;
}
lean_ctor_set(x_469, 0, x_342);
lean_ctor_set(x_469, 1, x_343);
lean_ctor_set(x_469, 2, x_344);
lean_ctor_set(x_469, 3, x_424);
lean_ctor_set_uint8(x_469, sizeof(void*)*4, x_468);
return x_469;
}
else
{
uint8_t x_470; 
x_470 = lean_ctor_get_uint8(x_466, sizeof(void*)*4);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; lean_object* x_484; 
x_471 = lean_ctor_get(x_424, 1);
lean_inc(x_471);
x_472 = lean_ctor_get(x_424, 2);
lean_inc(x_472);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_473 = x_424;
} else {
 lean_dec_ref(x_424);
 x_473 = lean_box(0);
}
x_474 = lean_ctor_get(x_466, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_466, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_466, 2);
lean_inc(x_476);
x_477 = lean_ctor_get(x_466, 3);
lean_inc(x_477);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 lean_ctor_release(x_466, 2);
 lean_ctor_release(x_466, 3);
 x_478 = x_466;
} else {
 lean_dec_ref(x_466);
 x_478 = lean_box(0);
}
x_479 = 1;
lean_inc(x_426);
if (lean_is_scalar(x_478)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_478;
}
lean_ctor_set(x_480, 0, x_342);
lean_ctor_set(x_480, 1, x_343);
lean_ctor_set(x_480, 2, x_344);
lean_ctor_set(x_480, 3, x_426);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_481 = x_426;
} else {
 lean_dec_ref(x_426);
 x_481 = lean_box(0);
}
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_479);
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(1, 4, 1);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_474);
lean_ctor_set(x_482, 1, x_475);
lean_ctor_set(x_482, 2, x_476);
lean_ctor_set(x_482, 3, x_477);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_479);
x_483 = 0;
if (lean_is_scalar(x_473)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_473;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_471);
lean_ctor_set(x_484, 2, x_472);
lean_ctor_set(x_484, 3, x_482);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_483);
return x_484;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; lean_object* x_496; 
x_485 = lean_ctor_get(x_424, 1);
lean_inc(x_485);
x_486 = lean_ctor_get(x_424, 2);
lean_inc(x_486);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_487 = x_424;
} else {
 lean_dec_ref(x_424);
 x_487 = lean_box(0);
}
x_488 = lean_ctor_get(x_426, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_426, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_426, 2);
lean_inc(x_490);
x_491 = lean_ctor_get(x_426, 3);
lean_inc(x_491);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_492 = x_426;
} else {
 lean_dec_ref(x_426);
 x_492 = lean_box(0);
}
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(1, 4, 1);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_488);
lean_ctor_set(x_493, 1, x_489);
lean_ctor_set(x_493, 2, x_490);
lean_ctor_set(x_493, 3, x_491);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_470);
if (lean_is_scalar(x_487)) {
 x_494 = lean_alloc_ctor(1, 4, 1);
} else {
 x_494 = x_487;
}
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_485);
lean_ctor_set(x_494, 2, x_486);
lean_ctor_set(x_494, 3, x_466);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_425);
x_495 = 1;
x_496 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_496, 0, x_342);
lean_ctor_set(x_496, 1, x_343);
lean_ctor_set(x_496, 2, x_344);
lean_ctor_set(x_496, 3, x_494);
lean_ctor_set_uint8(x_496, sizeof(void*)*4, x_495);
return x_496;
}
}
}
}
}
else
{
uint8_t x_497; lean_object* x_498; 
x_497 = 1;
x_498 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_498, 0, x_342);
lean_ctor_set(x_498, 1, x_343);
lean_ctor_set(x_498, 2, x_344);
lean_ctor_set(x_498, 3, x_424);
lean_ctor_set_uint8(x_498, sizeof(void*)*4, x_497);
return x_498;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_14 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_9, x_2, x_3);
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
x_17 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_12, x_2, x_3);
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
x_24 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_19, x_2, x_3);
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
x_29 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_22, x_2, x_3);
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
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_33, x_2, x_3);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*4);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_38, 3);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_38, 3);
lean_dec(x_43);
x_44 = lean_ctor_get(x_38, 0);
lean_dec(x_44);
lean_ctor_set(x_38, 0, x_41);
x_45 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_38, 1);
x_47 = lean_ctor_get(x_38, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_39);
x_49 = 1;
lean_ctor_set(x_1, 0, x_48);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_41, sizeof(void*)*4);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_38, 1);
x_53 = lean_ctor_get(x_38, 2);
x_54 = lean_ctor_get(x_38, 3);
lean_dec(x_54);
x_55 = lean_ctor_get(x_38, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_41);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_41, 0);
x_58 = lean_ctor_get(x_41, 1);
x_59 = lean_ctor_get(x_41, 2);
x_60 = lean_ctor_get(x_41, 3);
x_61 = 1;
lean_ctor_set(x_41, 3, x_57);
lean_ctor_set(x_41, 2, x_53);
lean_ctor_set(x_41, 1, x_52);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_61);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_60);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_61);
x_62 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_59);
lean_ctor_set(x_1, 1, x_58);
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_62);
return x_1;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; uint8_t x_69; 
x_63 = lean_ctor_get(x_41, 0);
x_64 = lean_ctor_get(x_41, 1);
x_65 = lean_ctor_get(x_41, 2);
x_66 = lean_ctor_get(x_41, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_41);
x_67 = 1;
x_68 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_68, 0, x_40);
lean_ctor_set(x_68, 1, x_52);
lean_ctor_set(x_68, 2, x_53);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set_uint8(x_68, sizeof(void*)*4, x_67);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_66);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_67);
x_69 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_65);
lean_ctor_set(x_1, 1, x_64);
lean_ctor_set(x_1, 0, x_68);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_70 = lean_ctor_get(x_38, 1);
x_71 = lean_ctor_get(x_38, 2);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_38);
x_72 = lean_ctor_get(x_41, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_41, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_41, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_41, 3);
lean_inc(x_75);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_76 = x_41;
} else {
 lean_dec_ref(x_41);
 x_76 = lean_box(0);
}
x_77 = 1;
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(1, 4, 1);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_40);
lean_ctor_set(x_78, 1, x_70);
lean_ctor_set(x_78, 2, x_71);
lean_ctor_set(x_78, 3, x_72);
lean_ctor_set_uint8(x_78, sizeof(void*)*4, x_77);
x_79 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_34);
lean_ctor_set(x_79, 2, x_35);
lean_ctor_set(x_79, 3, x_36);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_77);
x_80 = 0;
lean_ctor_set(x_1, 3, x_79);
lean_ctor_set(x_1, 2, x_74);
lean_ctor_set(x_1, 1, x_73);
lean_ctor_set(x_1, 0, x_78);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_80);
return x_1;
}
}
else
{
uint8_t x_81; 
lean_free_object(x_1);
x_81 = !lean_is_exclusive(x_41);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_41, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_41, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_41, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_41, 0);
lean_dec(x_85);
x_86 = 1;
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_86);
return x_41;
}
else
{
uint8_t x_87; lean_object* x_88; 
lean_dec(x_41);
x_87 = 1;
x_88 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_88, 0, x_38);
lean_ctor_set(x_88, 1, x_34);
lean_ctor_set(x_88, 2, x_35);
lean_ctor_set(x_88, 3, x_36);
lean_ctor_set_uint8(x_88, sizeof(void*)*4, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
x_89 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_38);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_91 = lean_ctor_get(x_38, 1);
x_92 = lean_ctor_get(x_38, 2);
x_93 = lean_ctor_get(x_38, 3);
x_94 = lean_ctor_get(x_38, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_40);
if (x_95 == 0)
{
uint8_t x_96; uint8_t x_97; 
x_96 = 1;
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_96);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_93);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_96);
x_97 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_92);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_40);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_97);
return x_1;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; uint8_t x_104; 
x_98 = lean_ctor_get(x_40, 0);
x_99 = lean_ctor_get(x_40, 1);
x_100 = lean_ctor_get(x_40, 2);
x_101 = lean_ctor_get(x_40, 3);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_40);
x_102 = 1;
x_103 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_99);
lean_ctor_set(x_103, 2, x_100);
lean_ctor_set(x_103, 3, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*4, x_102);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_93);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_102);
x_104 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_92);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_103);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_104);
return x_1;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_105 = lean_ctor_get(x_38, 1);
x_106 = lean_ctor_get(x_38, 2);
x_107 = lean_ctor_get(x_38, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_38);
x_108 = lean_ctor_get(x_40, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_40, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_40, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_40, 3);
lean_inc(x_111);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_112 = x_40;
} else {
 lean_dec_ref(x_40);
 x_112 = lean_box(0);
}
x_113 = 1;
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(1, 4, 1);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_109);
lean_ctor_set(x_114, 2, x_110);
lean_ctor_set(x_114, 3, x_111);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_113);
x_115 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_34);
lean_ctor_set(x_115, 2, x_35);
lean_ctor_set(x_115, 3, x_36);
lean_ctor_set_uint8(x_115, sizeof(void*)*4, x_113);
x_116 = 0;
lean_ctor_set(x_1, 3, x_115);
lean_ctor_set(x_1, 2, x_106);
lean_ctor_set(x_1, 1, x_105);
lean_ctor_set(x_1, 0, x_114);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_116);
return x_1;
}
}
else
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_38, 3);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
lean_free_object(x_1);
x_118 = !lean_is_exclusive(x_40);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_119 = lean_ctor_get(x_40, 3);
lean_dec(x_119);
x_120 = lean_ctor_get(x_40, 2);
lean_dec(x_120);
x_121 = lean_ctor_get(x_40, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_40, 0);
lean_dec(x_122);
x_123 = 1;
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_123);
return x_40;
}
else
{
uint8_t x_124; lean_object* x_125; 
lean_dec(x_40);
x_124 = 1;
x_125 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_125, 0, x_38);
lean_ctor_set(x_125, 1, x_34);
lean_ctor_set(x_125, 2, x_35);
lean_ctor_set(x_125, 3, x_36);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_124);
return x_125;
}
}
else
{
uint8_t x_126; 
x_126 = lean_ctor_get_uint8(x_117, sizeof(void*)*4);
if (x_126 == 0)
{
uint8_t x_127; 
lean_free_object(x_1);
x_127 = !lean_is_exclusive(x_38);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_38, 1);
x_129 = lean_ctor_get(x_38, 2);
x_130 = lean_ctor_get(x_38, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_38, 0);
lean_dec(x_131);
x_132 = !lean_is_exclusive(x_117);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; 
x_133 = lean_ctor_get(x_117, 0);
x_134 = lean_ctor_get(x_117, 1);
x_135 = lean_ctor_get(x_117, 2);
x_136 = lean_ctor_get(x_117, 3);
x_137 = 1;
lean_inc(x_40);
lean_ctor_set(x_117, 3, x_133);
lean_ctor_set(x_117, 2, x_129);
lean_ctor_set(x_117, 1, x_128);
lean_ctor_set(x_117, 0, x_40);
x_138 = !lean_is_exclusive(x_40);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_139 = lean_ctor_get(x_40, 3);
lean_dec(x_139);
x_140 = lean_ctor_get(x_40, 2);
lean_dec(x_140);
x_141 = lean_ctor_get(x_40, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_40, 0);
lean_dec(x_142);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_137);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 0, x_136);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_137);
x_143 = 0;
lean_ctor_set(x_38, 3, x_40);
lean_ctor_set(x_38, 2, x_135);
lean_ctor_set(x_38, 1, x_134);
lean_ctor_set(x_38, 0, x_117);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_143);
return x_38;
}
else
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_40);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_137);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_136);
lean_ctor_set(x_144, 1, x_34);
lean_ctor_set(x_144, 2, x_35);
lean_ctor_set(x_144, 3, x_36);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_137);
x_145 = 0;
lean_ctor_set(x_38, 3, x_144);
lean_ctor_set(x_38, 2, x_135);
lean_ctor_set(x_38, 1, x_134);
lean_ctor_set(x_38, 0, x_117);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_145);
return x_38;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_146 = lean_ctor_get(x_117, 0);
x_147 = lean_ctor_get(x_117, 1);
x_148 = lean_ctor_get(x_117, 2);
x_149 = lean_ctor_get(x_117, 3);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_117);
x_150 = 1;
lean_inc(x_40);
x_151 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_151, 0, x_40);
lean_ctor_set(x_151, 1, x_128);
lean_ctor_set(x_151, 2, x_129);
lean_ctor_set(x_151, 3, x_146);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_152 = x_40;
} else {
 lean_dec_ref(x_40);
 x_152 = lean_box(0);
}
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_150);
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 4, 1);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_34);
lean_ctor_set(x_153, 2, x_35);
lean_ctor_set(x_153, 3, x_36);
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_150);
x_154 = 0;
lean_ctor_set(x_38, 3, x_153);
lean_ctor_set(x_38, 2, x_148);
lean_ctor_set(x_38, 1, x_147);
lean_ctor_set(x_38, 0, x_151);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_154);
return x_38;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; 
x_155 = lean_ctor_get(x_38, 1);
x_156 = lean_ctor_get(x_38, 2);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_38);
x_157 = lean_ctor_get(x_117, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_117, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_117, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_117, 3);
lean_inc(x_160);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 x_161 = x_117;
} else {
 lean_dec_ref(x_117);
 x_161 = lean_box(0);
}
x_162 = 1;
lean_inc(x_40);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(1, 4, 1);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_40);
lean_ctor_set(x_163, 1, x_155);
lean_ctor_set(x_163, 2, x_156);
lean_ctor_set(x_163, 3, x_157);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_164 = x_40;
} else {
 lean_dec_ref(x_40);
 x_164 = lean_box(0);
}
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_162);
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 4, 1);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_160);
lean_ctor_set(x_165, 1, x_34);
lean_ctor_set(x_165, 2, x_35);
lean_ctor_set(x_165, 3, x_36);
lean_ctor_set_uint8(x_165, sizeof(void*)*4, x_162);
x_166 = 0;
x_167 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_167, 0, x_163);
lean_ctor_set(x_167, 1, x_158);
lean_ctor_set(x_167, 2, x_159);
lean_ctor_set(x_167, 3, x_165);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_166);
return x_167;
}
}
else
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_38);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_ctor_get(x_38, 3);
lean_dec(x_169);
x_170 = lean_ctor_get(x_38, 0);
lean_dec(x_170);
x_171 = !lean_is_exclusive(x_40);
if (x_171 == 0)
{
uint8_t x_172; 
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_126);
x_172 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_172);
return x_1;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_173 = lean_ctor_get(x_40, 0);
x_174 = lean_ctor_get(x_40, 1);
x_175 = lean_ctor_get(x_40, 2);
x_176 = lean_ctor_get(x_40, 3);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_40);
x_177 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_174);
lean_ctor_set(x_177, 2, x_175);
lean_ctor_set(x_177, 3, x_176);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_126);
lean_ctor_set(x_38, 0, x_177);
x_178 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_178);
return x_1;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_179 = lean_ctor_get(x_38, 1);
x_180 = lean_ctor_get(x_38, 2);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_38);
x_181 = lean_ctor_get(x_40, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_40, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_40, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_40, 3);
lean_inc(x_184);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_185 = x_40;
} else {
 lean_dec_ref(x_40);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 4, 1);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_181);
lean_ctor_set(x_186, 1, x_182);
lean_ctor_set(x_186, 2, x_183);
lean_ctor_set(x_186, 3, x_184);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_126);
x_187 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_179);
lean_ctor_set(x_187, 2, x_180);
lean_ctor_set(x_187, 3, x_117);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_39);
x_188 = 1;
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_189; 
x_189 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
case 1:
{
uint8_t x_190; 
lean_dec(x_35);
lean_dec(x_34);
x_190 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_190);
return x_1;
}
default: 
{
lean_object* x_191; uint8_t x_192; 
x_191 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_36, x_2, x_3);
x_192 = lean_ctor_get_uint8(x_191, sizeof(void*)*4);
if (x_192 == 0)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_191, 3);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_191);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_196 = lean_ctor_get(x_191, 3);
lean_dec(x_196);
x_197 = lean_ctor_get(x_191, 0);
lean_dec(x_197);
lean_ctor_set(x_191, 0, x_194);
x_198 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_198);
return x_1;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_199 = lean_ctor_get(x_191, 1);
x_200 = lean_ctor_get(x_191, 2);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_191);
x_201 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_201, 0, x_194);
lean_ctor_set(x_201, 1, x_199);
lean_ctor_set(x_201, 2, x_200);
lean_ctor_set(x_201, 3, x_194);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_192);
x_202 = 1;
lean_ctor_set(x_1, 3, x_201);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
}
}
else
{
uint8_t x_203; 
x_203 = lean_ctor_get_uint8(x_194, sizeof(void*)*4);
if (x_203 == 0)
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_191);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_191, 1);
x_206 = lean_ctor_get(x_191, 2);
x_207 = lean_ctor_get(x_191, 3);
lean_dec(x_207);
x_208 = lean_ctor_get(x_191, 0);
lean_dec(x_208);
x_209 = !lean_is_exclusive(x_194);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; 
x_210 = lean_ctor_get(x_194, 0);
x_211 = lean_ctor_get(x_194, 1);
x_212 = lean_ctor_get(x_194, 2);
x_213 = lean_ctor_get(x_194, 3);
x_214 = 1;
lean_ctor_set(x_194, 3, x_193);
lean_ctor_set(x_194, 2, x_35);
lean_ctor_set(x_194, 1, x_34);
lean_ctor_set(x_194, 0, x_33);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_214);
lean_ctor_set(x_191, 3, x_213);
lean_ctor_set(x_191, 2, x_212);
lean_ctor_set(x_191, 1, x_211);
lean_ctor_set(x_191, 0, x_210);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_214);
x_215 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_215);
return x_1;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; uint8_t x_222; 
x_216 = lean_ctor_get(x_194, 0);
x_217 = lean_ctor_get(x_194, 1);
x_218 = lean_ctor_get(x_194, 2);
x_219 = lean_ctor_get(x_194, 3);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_194);
x_220 = 1;
x_221 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_221, 0, x_33);
lean_ctor_set(x_221, 1, x_34);
lean_ctor_set(x_221, 2, x_35);
lean_ctor_set(x_221, 3, x_193);
lean_ctor_set_uint8(x_221, sizeof(void*)*4, x_220);
lean_ctor_set(x_191, 3, x_219);
lean_ctor_set(x_191, 2, x_218);
lean_ctor_set(x_191, 1, x_217);
lean_ctor_set(x_191, 0, x_216);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_220);
x_222 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_221);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_222);
return x_1;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_223 = lean_ctor_get(x_191, 1);
x_224 = lean_ctor_get(x_191, 2);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_191);
x_225 = lean_ctor_get(x_194, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_194, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_194, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_194, 3);
lean_inc(x_228);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_229 = x_194;
} else {
 lean_dec_ref(x_194);
 x_229 = lean_box(0);
}
x_230 = 1;
if (lean_is_scalar(x_229)) {
 x_231 = lean_alloc_ctor(1, 4, 1);
} else {
 x_231 = x_229;
}
lean_ctor_set(x_231, 0, x_33);
lean_ctor_set(x_231, 1, x_34);
lean_ctor_set(x_231, 2, x_35);
lean_ctor_set(x_231, 3, x_193);
lean_ctor_set_uint8(x_231, sizeof(void*)*4, x_230);
x_232 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_232, 0, x_225);
lean_ctor_set(x_232, 1, x_226);
lean_ctor_set(x_232, 2, x_227);
lean_ctor_set(x_232, 3, x_228);
lean_ctor_set_uint8(x_232, sizeof(void*)*4, x_230);
x_233 = 0;
lean_ctor_set(x_1, 3, x_232);
lean_ctor_set(x_1, 2, x_224);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_1, 0, x_231);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
}
else
{
uint8_t x_234; 
lean_free_object(x_1);
x_234 = !lean_is_exclusive(x_194);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_235 = lean_ctor_get(x_194, 3);
lean_dec(x_235);
x_236 = lean_ctor_get(x_194, 2);
lean_dec(x_236);
x_237 = lean_ctor_get(x_194, 1);
lean_dec(x_237);
x_238 = lean_ctor_get(x_194, 0);
lean_dec(x_238);
x_239 = 1;
lean_ctor_set(x_194, 3, x_191);
lean_ctor_set(x_194, 2, x_35);
lean_ctor_set(x_194, 1, x_34);
lean_ctor_set(x_194, 0, x_33);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_239);
return x_194;
}
else
{
uint8_t x_240; lean_object* x_241; 
lean_dec(x_194);
x_240 = 1;
x_241 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_241, 0, x_33);
lean_ctor_set(x_241, 1, x_34);
lean_ctor_set(x_241, 2, x_35);
lean_ctor_set(x_241, 3, x_191);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_240);
return x_241;
}
}
}
}
else
{
uint8_t x_242; 
x_242 = lean_ctor_get_uint8(x_193, sizeof(void*)*4);
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = !lean_is_exclusive(x_191);
if (x_243 == 0)
{
lean_object* x_244; uint8_t x_245; 
x_244 = lean_ctor_get(x_191, 0);
lean_dec(x_244);
x_245 = !lean_is_exclusive(x_193);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_251; 
x_246 = lean_ctor_get(x_193, 0);
x_247 = lean_ctor_get(x_193, 1);
x_248 = lean_ctor_get(x_193, 2);
x_249 = lean_ctor_get(x_193, 3);
x_250 = 1;
lean_ctor_set(x_193, 3, x_246);
lean_ctor_set(x_193, 2, x_35);
lean_ctor_set(x_193, 1, x_34);
lean_ctor_set(x_193, 0, x_33);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_250);
lean_ctor_set(x_191, 0, x_249);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_250);
x_251 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_248);
lean_ctor_set(x_1, 1, x_247);
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_251);
return x_1;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; uint8_t x_258; 
x_252 = lean_ctor_get(x_193, 0);
x_253 = lean_ctor_get(x_193, 1);
x_254 = lean_ctor_get(x_193, 2);
x_255 = lean_ctor_get(x_193, 3);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_193);
x_256 = 1;
x_257 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_257, 0, x_33);
lean_ctor_set(x_257, 1, x_34);
lean_ctor_set(x_257, 2, x_35);
lean_ctor_set(x_257, 3, x_252);
lean_ctor_set_uint8(x_257, sizeof(void*)*4, x_256);
lean_ctor_set(x_191, 0, x_255);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_256);
x_258 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_254);
lean_ctor_set(x_1, 1, x_253);
lean_ctor_set(x_1, 0, x_257);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_258);
return x_1;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_259 = lean_ctor_get(x_191, 1);
x_260 = lean_ctor_get(x_191, 2);
x_261 = lean_ctor_get(x_191, 3);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_191);
x_262 = lean_ctor_get(x_193, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_193, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_193, 2);
lean_inc(x_264);
x_265 = lean_ctor_get(x_193, 3);
lean_inc(x_265);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_266 = x_193;
} else {
 lean_dec_ref(x_193);
 x_266 = lean_box(0);
}
x_267 = 1;
if (lean_is_scalar(x_266)) {
 x_268 = lean_alloc_ctor(1, 4, 1);
} else {
 x_268 = x_266;
}
lean_ctor_set(x_268, 0, x_33);
lean_ctor_set(x_268, 1, x_34);
lean_ctor_set(x_268, 2, x_35);
lean_ctor_set(x_268, 3, x_262);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_267);
x_269 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_269, 0, x_265);
lean_ctor_set(x_269, 1, x_259);
lean_ctor_set(x_269, 2, x_260);
lean_ctor_set(x_269, 3, x_261);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_267);
x_270 = 0;
lean_ctor_set(x_1, 3, x_269);
lean_ctor_set(x_1, 2, x_264);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_268);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
return x_1;
}
}
else
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_191, 3);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
lean_free_object(x_1);
x_272 = !lean_is_exclusive(x_193);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_273 = lean_ctor_get(x_193, 3);
lean_dec(x_273);
x_274 = lean_ctor_get(x_193, 2);
lean_dec(x_274);
x_275 = lean_ctor_get(x_193, 1);
lean_dec(x_275);
x_276 = lean_ctor_get(x_193, 0);
lean_dec(x_276);
x_277 = 1;
lean_ctor_set(x_193, 3, x_191);
lean_ctor_set(x_193, 2, x_35);
lean_ctor_set(x_193, 1, x_34);
lean_ctor_set(x_193, 0, x_33);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_277);
return x_193;
}
else
{
uint8_t x_278; lean_object* x_279; 
lean_dec(x_193);
x_278 = 1;
x_279 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_279, 0, x_33);
lean_ctor_set(x_279, 1, x_34);
lean_ctor_set(x_279, 2, x_35);
lean_ctor_set(x_279, 3, x_191);
lean_ctor_set_uint8(x_279, sizeof(void*)*4, x_278);
return x_279;
}
}
else
{
uint8_t x_280; 
x_280 = lean_ctor_get_uint8(x_271, sizeof(void*)*4);
if (x_280 == 0)
{
uint8_t x_281; 
lean_free_object(x_1);
x_281 = !lean_is_exclusive(x_191);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_282 = lean_ctor_get(x_191, 3);
lean_dec(x_282);
x_283 = lean_ctor_get(x_191, 0);
lean_dec(x_283);
x_284 = !lean_is_exclusive(x_271);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_290; 
x_285 = lean_ctor_get(x_271, 0);
x_286 = lean_ctor_get(x_271, 1);
x_287 = lean_ctor_get(x_271, 2);
x_288 = lean_ctor_get(x_271, 3);
x_289 = 1;
lean_inc(x_193);
lean_ctor_set(x_271, 3, x_193);
lean_ctor_set(x_271, 2, x_35);
lean_ctor_set(x_271, 1, x_34);
lean_ctor_set(x_271, 0, x_33);
x_290 = !lean_is_exclusive(x_193);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_291 = lean_ctor_get(x_193, 3);
lean_dec(x_291);
x_292 = lean_ctor_get(x_193, 2);
lean_dec(x_292);
x_293 = lean_ctor_get(x_193, 1);
lean_dec(x_293);
x_294 = lean_ctor_get(x_193, 0);
lean_dec(x_294);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_289);
lean_ctor_set(x_193, 3, x_288);
lean_ctor_set(x_193, 2, x_287);
lean_ctor_set(x_193, 1, x_286);
lean_ctor_set(x_193, 0, x_285);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_289);
x_295 = 0;
lean_ctor_set(x_191, 3, x_193);
lean_ctor_set(x_191, 0, x_271);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_295);
return x_191;
}
else
{
lean_object* x_296; uint8_t x_297; 
lean_dec(x_193);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_289);
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_285);
lean_ctor_set(x_296, 1, x_286);
lean_ctor_set(x_296, 2, x_287);
lean_ctor_set(x_296, 3, x_288);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_289);
x_297 = 0;
lean_ctor_set(x_191, 3, x_296);
lean_ctor_set(x_191, 0, x_271);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_297);
return x_191;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_298 = lean_ctor_get(x_271, 0);
x_299 = lean_ctor_get(x_271, 1);
x_300 = lean_ctor_get(x_271, 2);
x_301 = lean_ctor_get(x_271, 3);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_271);
x_302 = 1;
lean_inc(x_193);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_33);
lean_ctor_set(x_303, 1, x_34);
lean_ctor_set(x_303, 2, x_35);
lean_ctor_set(x_303, 3, x_193);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_304 = x_193;
} else {
 lean_dec_ref(x_193);
 x_304 = lean_box(0);
}
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_302);
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 4, 1);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_298);
lean_ctor_set(x_305, 1, x_299);
lean_ctor_set(x_305, 2, x_300);
lean_ctor_set(x_305, 3, x_301);
lean_ctor_set_uint8(x_305, sizeof(void*)*4, x_302);
x_306 = 0;
lean_ctor_set(x_191, 3, x_305);
lean_ctor_set(x_191, 0, x_303);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_306);
return x_191;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; 
x_307 = lean_ctor_get(x_191, 1);
x_308 = lean_ctor_get(x_191, 2);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_191);
x_309 = lean_ctor_get(x_271, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_271, 1);
lean_inc(x_310);
x_311 = lean_ctor_get(x_271, 2);
lean_inc(x_311);
x_312 = lean_ctor_get(x_271, 3);
lean_inc(x_312);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 lean_ctor_release(x_271, 3);
 x_313 = x_271;
} else {
 lean_dec_ref(x_271);
 x_313 = lean_box(0);
}
x_314 = 1;
lean_inc(x_193);
if (lean_is_scalar(x_313)) {
 x_315 = lean_alloc_ctor(1, 4, 1);
} else {
 x_315 = x_313;
}
lean_ctor_set(x_315, 0, x_33);
lean_ctor_set(x_315, 1, x_34);
lean_ctor_set(x_315, 2, x_35);
lean_ctor_set(x_315, 3, x_193);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_316 = x_193;
} else {
 lean_dec_ref(x_193);
 x_316 = lean_box(0);
}
lean_ctor_set_uint8(x_315, sizeof(void*)*4, x_314);
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 4, 1);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_310);
lean_ctor_set(x_317, 2, x_311);
lean_ctor_set(x_317, 3, x_312);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_314);
x_318 = 0;
x_319 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_319, 0, x_315);
lean_ctor_set(x_319, 1, x_307);
lean_ctor_set(x_319, 2, x_308);
lean_ctor_set(x_319, 3, x_317);
lean_ctor_set_uint8(x_319, sizeof(void*)*4, x_318);
return x_319;
}
}
else
{
uint8_t x_320; 
x_320 = !lean_is_exclusive(x_191);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_321 = lean_ctor_get(x_191, 3);
lean_dec(x_321);
x_322 = lean_ctor_get(x_191, 0);
lean_dec(x_322);
x_323 = !lean_is_exclusive(x_193);
if (x_323 == 0)
{
uint8_t x_324; 
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_280);
x_324 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_324);
return x_1;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_325 = lean_ctor_get(x_193, 0);
x_326 = lean_ctor_get(x_193, 1);
x_327 = lean_ctor_get(x_193, 2);
x_328 = lean_ctor_get(x_193, 3);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_193);
x_329 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_329, 0, x_325);
lean_ctor_set(x_329, 1, x_326);
lean_ctor_set(x_329, 2, x_327);
lean_ctor_set(x_329, 3, x_328);
lean_ctor_set_uint8(x_329, sizeof(void*)*4, x_280);
lean_ctor_set(x_191, 0, x_329);
x_330 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_330);
return x_1;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_331 = lean_ctor_get(x_191, 1);
x_332 = lean_ctor_get(x_191, 2);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_191);
x_333 = lean_ctor_get(x_193, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_193, 1);
lean_inc(x_334);
x_335 = lean_ctor_get(x_193, 2);
lean_inc(x_335);
x_336 = lean_ctor_get(x_193, 3);
lean_inc(x_336);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_337 = x_193;
} else {
 lean_dec_ref(x_193);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_334);
lean_ctor_set(x_338, 2, x_335);
lean_ctor_set(x_338, 3, x_336);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_280);
x_339 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_331);
lean_ctor_set(x_339, 2, x_332);
lean_ctor_set(x_339, 3, x_271);
lean_ctor_set_uint8(x_339, sizeof(void*)*4, x_192);
x_340 = 1;
lean_ctor_set(x_1, 3, x_339);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_340);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_341; 
x_341 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_341);
return x_1;
}
}
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_342 = lean_ctor_get(x_1, 0);
x_343 = lean_ctor_get(x_1, 1);
x_344 = lean_ctor_get(x_1, 2);
x_345 = lean_ctor_get(x_1, 3);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_1);
x_346 = l_Lean_Name_quickCmp(x_2, x_343);
switch (x_346) {
case 0:
{
lean_object* x_347; uint8_t x_348; 
x_347 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_342, x_2, x_3);
x_348 = lean_ctor_get_uint8(x_347, sizeof(void*)*4);
if (x_348 == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_347, 0);
lean_inc(x_349);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; 
x_350 = lean_ctor_get(x_347, 3);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; 
x_351 = lean_ctor_get(x_347, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_347, 2);
lean_inc(x_352);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_353 = x_347;
} else {
 lean_dec_ref(x_347);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 4, 1);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_350);
lean_ctor_set(x_354, 1, x_351);
lean_ctor_set(x_354, 2, x_352);
lean_ctor_set(x_354, 3, x_350);
lean_ctor_set_uint8(x_354, sizeof(void*)*4, x_348);
x_355 = 1;
x_356 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_343);
lean_ctor_set(x_356, 2, x_344);
lean_ctor_set(x_356, 3, x_345);
lean_ctor_set_uint8(x_356, sizeof(void*)*4, x_355);
return x_356;
}
else
{
uint8_t x_357; 
x_357 = lean_ctor_get_uint8(x_350, sizeof(void*)*4);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_358 = lean_ctor_get(x_347, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_347, 2);
lean_inc(x_359);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_360 = x_347;
} else {
 lean_dec_ref(x_347);
 x_360 = lean_box(0);
}
x_361 = lean_ctor_get(x_350, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_350, 1);
lean_inc(x_362);
x_363 = lean_ctor_get(x_350, 2);
lean_inc(x_363);
x_364 = lean_ctor_get(x_350, 3);
lean_inc(x_364);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_365 = x_350;
} else {
 lean_dec_ref(x_350);
 x_365 = lean_box(0);
}
x_366 = 1;
if (lean_is_scalar(x_365)) {
 x_367 = lean_alloc_ctor(1, 4, 1);
} else {
 x_367 = x_365;
}
lean_ctor_set(x_367, 0, x_349);
lean_ctor_set(x_367, 1, x_358);
lean_ctor_set(x_367, 2, x_359);
lean_ctor_set(x_367, 3, x_361);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_366);
if (lean_is_scalar(x_360)) {
 x_368 = lean_alloc_ctor(1, 4, 1);
} else {
 x_368 = x_360;
}
lean_ctor_set(x_368, 0, x_364);
lean_ctor_set(x_368, 1, x_343);
lean_ctor_set(x_368, 2, x_344);
lean_ctor_set(x_368, 3, x_345);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_366);
x_369 = 0;
x_370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_362);
lean_ctor_set(x_370, 2, x_363);
lean_ctor_set(x_370, 3, x_368);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_369);
return x_370;
}
else
{
lean_object* x_371; uint8_t x_372; lean_object* x_373; 
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_371 = x_350;
} else {
 lean_dec_ref(x_350);
 x_371 = lean_box(0);
}
x_372 = 1;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_347);
lean_ctor_set(x_373, 1, x_343);
lean_ctor_set(x_373, 2, x_344);
lean_ctor_set(x_373, 3, x_345);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
return x_373;
}
}
}
else
{
uint8_t x_374; 
x_374 = lean_ctor_get_uint8(x_349, sizeof(void*)*4);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; 
x_375 = lean_ctor_get(x_347, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_347, 2);
lean_inc(x_376);
x_377 = lean_ctor_get(x_347, 3);
lean_inc(x_377);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_378 = x_347;
} else {
 lean_dec_ref(x_347);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_349, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_349, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_349, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_349, 3);
lean_inc(x_382);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_383 = x_349;
} else {
 lean_dec_ref(x_349);
 x_383 = lean_box(0);
}
x_384 = 1;
if (lean_is_scalar(x_383)) {
 x_385 = lean_alloc_ctor(1, 4, 1);
} else {
 x_385 = x_383;
}
lean_ctor_set(x_385, 0, x_379);
lean_ctor_set(x_385, 1, x_380);
lean_ctor_set(x_385, 2, x_381);
lean_ctor_set(x_385, 3, x_382);
lean_ctor_set_uint8(x_385, sizeof(void*)*4, x_384);
if (lean_is_scalar(x_378)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_378;
}
lean_ctor_set(x_386, 0, x_377);
lean_ctor_set(x_386, 1, x_343);
lean_ctor_set(x_386, 2, x_344);
lean_ctor_set(x_386, 3, x_345);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_384);
x_387 = 0;
x_388 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_375);
lean_ctor_set(x_388, 2, x_376);
lean_ctor_set(x_388, 3, x_386);
lean_ctor_set_uint8(x_388, sizeof(void*)*4, x_387);
return x_388;
}
else
{
lean_object* x_389; 
x_389 = lean_ctor_get(x_347, 3);
lean_inc(x_389);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; uint8_t x_391; lean_object* x_392; 
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_390 = x_349;
} else {
 lean_dec_ref(x_349);
 x_390 = lean_box(0);
}
x_391 = 1;
if (lean_is_scalar(x_390)) {
 x_392 = lean_alloc_ctor(1, 4, 1);
} else {
 x_392 = x_390;
}
lean_ctor_set(x_392, 0, x_347);
lean_ctor_set(x_392, 1, x_343);
lean_ctor_set(x_392, 2, x_344);
lean_ctor_set(x_392, 3, x_345);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_391);
return x_392;
}
else
{
uint8_t x_393; 
x_393 = lean_ctor_get_uint8(x_389, sizeof(void*)*4);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; 
x_394 = lean_ctor_get(x_347, 1);
lean_inc(x_394);
x_395 = lean_ctor_get(x_347, 2);
lean_inc(x_395);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_396 = x_347;
} else {
 lean_dec_ref(x_347);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_389, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_389, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_389, 2);
lean_inc(x_399);
x_400 = lean_ctor_get(x_389, 3);
lean_inc(x_400);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 lean_ctor_release(x_389, 2);
 lean_ctor_release(x_389, 3);
 x_401 = x_389;
} else {
 lean_dec_ref(x_389);
 x_401 = lean_box(0);
}
x_402 = 1;
lean_inc(x_349);
if (lean_is_scalar(x_401)) {
 x_403 = lean_alloc_ctor(1, 4, 1);
} else {
 x_403 = x_401;
}
lean_ctor_set(x_403, 0, x_349);
lean_ctor_set(x_403, 1, x_394);
lean_ctor_set(x_403, 2, x_395);
lean_ctor_set(x_403, 3, x_397);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_404 = x_349;
} else {
 lean_dec_ref(x_349);
 x_404 = lean_box(0);
}
lean_ctor_set_uint8(x_403, sizeof(void*)*4, x_402);
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(1, 4, 1);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_400);
lean_ctor_set(x_405, 1, x_343);
lean_ctor_set(x_405, 2, x_344);
lean_ctor_set(x_405, 3, x_345);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_402);
x_406 = 0;
if (lean_is_scalar(x_396)) {
 x_407 = lean_alloc_ctor(1, 4, 1);
} else {
 x_407 = x_396;
}
lean_ctor_set(x_407, 0, x_403);
lean_ctor_set(x_407, 1, x_398);
lean_ctor_set(x_407, 2, x_399);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
return x_407;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; 
x_408 = lean_ctor_get(x_347, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_347, 2);
lean_inc(x_409);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_410 = x_347;
} else {
 lean_dec_ref(x_347);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_349, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_349, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_349, 2);
lean_inc(x_413);
x_414 = lean_ctor_get(x_349, 3);
lean_inc(x_414);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_415 = x_349;
} else {
 lean_dec_ref(x_349);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(1, 4, 1);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_411);
lean_ctor_set(x_416, 1, x_412);
lean_ctor_set(x_416, 2, x_413);
lean_ctor_set(x_416, 3, x_414);
lean_ctor_set_uint8(x_416, sizeof(void*)*4, x_393);
if (lean_is_scalar(x_410)) {
 x_417 = lean_alloc_ctor(1, 4, 1);
} else {
 x_417 = x_410;
}
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_408);
lean_ctor_set(x_417, 2, x_409);
lean_ctor_set(x_417, 3, x_389);
lean_ctor_set_uint8(x_417, sizeof(void*)*4, x_348);
x_418 = 1;
x_419 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_343);
lean_ctor_set(x_419, 2, x_344);
lean_ctor_set(x_419, 3, x_345);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
return x_419;
}
}
}
}
}
else
{
uint8_t x_420; lean_object* x_421; 
x_420 = 1;
x_421 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_421, 0, x_347);
lean_ctor_set(x_421, 1, x_343);
lean_ctor_set(x_421, 2, x_344);
lean_ctor_set(x_421, 3, x_345);
lean_ctor_set_uint8(x_421, sizeof(void*)*4, x_420);
return x_421;
}
}
case 1:
{
uint8_t x_422; lean_object* x_423; 
lean_dec(x_344);
lean_dec(x_343);
x_422 = 1;
x_423 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_423, 0, x_342);
lean_ctor_set(x_423, 1, x_2);
lean_ctor_set(x_423, 2, x_3);
lean_ctor_set(x_423, 3, x_345);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
return x_423;
}
default: 
{
lean_object* x_424; uint8_t x_425; 
x_424 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_345, x_2, x_3);
x_425 = lean_ctor_get_uint8(x_424, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; 
x_426 = lean_ctor_get(x_424, 0);
lean_inc(x_426);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; 
x_427 = lean_ctor_get(x_424, 3);
lean_inc(x_427);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; 
x_428 = lean_ctor_get(x_424, 1);
lean_inc(x_428);
x_429 = lean_ctor_get(x_424, 2);
lean_inc(x_429);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_430 = x_424;
} else {
 lean_dec_ref(x_424);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 4, 1);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_427);
lean_ctor_set(x_431, 1, x_428);
lean_ctor_set(x_431, 2, x_429);
lean_ctor_set(x_431, 3, x_427);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_425);
x_432 = 1;
x_433 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_433, 0, x_342);
lean_ctor_set(x_433, 1, x_343);
lean_ctor_set(x_433, 2, x_344);
lean_ctor_set(x_433, 3, x_431);
lean_ctor_set_uint8(x_433, sizeof(void*)*4, x_432);
return x_433;
}
else
{
uint8_t x_434; 
x_434 = lean_ctor_get_uint8(x_427, sizeof(void*)*4);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; 
x_435 = lean_ctor_get(x_424, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_424, 2);
lean_inc(x_436);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_437 = x_424;
} else {
 lean_dec_ref(x_424);
 x_437 = lean_box(0);
}
x_438 = lean_ctor_get(x_427, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_427, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_427, 2);
lean_inc(x_440);
x_441 = lean_ctor_get(x_427, 3);
lean_inc(x_441);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_442 = x_427;
} else {
 lean_dec_ref(x_427);
 x_442 = lean_box(0);
}
x_443 = 1;
if (lean_is_scalar(x_442)) {
 x_444 = lean_alloc_ctor(1, 4, 1);
} else {
 x_444 = x_442;
}
lean_ctor_set(x_444, 0, x_342);
lean_ctor_set(x_444, 1, x_343);
lean_ctor_set(x_444, 2, x_344);
lean_ctor_set(x_444, 3, x_426);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_443);
if (lean_is_scalar(x_437)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_437;
}
lean_ctor_set(x_445, 0, x_438);
lean_ctor_set(x_445, 1, x_439);
lean_ctor_set(x_445, 2, x_440);
lean_ctor_set(x_445, 3, x_441);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_443);
x_446 = 0;
x_447 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_447, 0, x_444);
lean_ctor_set(x_447, 1, x_435);
lean_ctor_set(x_447, 2, x_436);
lean_ctor_set(x_447, 3, x_445);
lean_ctor_set_uint8(x_447, sizeof(void*)*4, x_446);
return x_447;
}
else
{
lean_object* x_448; uint8_t x_449; lean_object* x_450; 
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_448 = x_427;
} else {
 lean_dec_ref(x_427);
 x_448 = lean_box(0);
}
x_449 = 1;
if (lean_is_scalar(x_448)) {
 x_450 = lean_alloc_ctor(1, 4, 1);
} else {
 x_450 = x_448;
}
lean_ctor_set(x_450, 0, x_342);
lean_ctor_set(x_450, 1, x_343);
lean_ctor_set(x_450, 2, x_344);
lean_ctor_set(x_450, 3, x_424);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
return x_450;
}
}
}
else
{
uint8_t x_451; 
x_451 = lean_ctor_get_uint8(x_426, sizeof(void*)*4);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; lean_object* x_465; 
x_452 = lean_ctor_get(x_424, 1);
lean_inc(x_452);
x_453 = lean_ctor_get(x_424, 2);
lean_inc(x_453);
x_454 = lean_ctor_get(x_424, 3);
lean_inc(x_454);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_455 = x_424;
} else {
 lean_dec_ref(x_424);
 x_455 = lean_box(0);
}
x_456 = lean_ctor_get(x_426, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_426, 1);
lean_inc(x_457);
x_458 = lean_ctor_get(x_426, 2);
lean_inc(x_458);
x_459 = lean_ctor_get(x_426, 3);
lean_inc(x_459);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_460 = x_426;
} else {
 lean_dec_ref(x_426);
 x_460 = lean_box(0);
}
x_461 = 1;
if (lean_is_scalar(x_460)) {
 x_462 = lean_alloc_ctor(1, 4, 1);
} else {
 x_462 = x_460;
}
lean_ctor_set(x_462, 0, x_342);
lean_ctor_set(x_462, 1, x_343);
lean_ctor_set(x_462, 2, x_344);
lean_ctor_set(x_462, 3, x_456);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
if (lean_is_scalar(x_455)) {
 x_463 = lean_alloc_ctor(1, 4, 1);
} else {
 x_463 = x_455;
}
lean_ctor_set(x_463, 0, x_459);
lean_ctor_set(x_463, 1, x_452);
lean_ctor_set(x_463, 2, x_453);
lean_ctor_set(x_463, 3, x_454);
lean_ctor_set_uint8(x_463, sizeof(void*)*4, x_461);
x_464 = 0;
x_465 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_457);
lean_ctor_set(x_465, 2, x_458);
lean_ctor_set(x_465, 3, x_463);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_464);
return x_465;
}
else
{
lean_object* x_466; 
x_466 = lean_ctor_get(x_424, 3);
lean_inc(x_466);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; uint8_t x_468; lean_object* x_469; 
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_467 = x_426;
} else {
 lean_dec_ref(x_426);
 x_467 = lean_box(0);
}
x_468 = 1;
if (lean_is_scalar(x_467)) {
 x_469 = lean_alloc_ctor(1, 4, 1);
} else {
 x_469 = x_467;
}
lean_ctor_set(x_469, 0, x_342);
lean_ctor_set(x_469, 1, x_343);
lean_ctor_set(x_469, 2, x_344);
lean_ctor_set(x_469, 3, x_424);
lean_ctor_set_uint8(x_469, sizeof(void*)*4, x_468);
return x_469;
}
else
{
uint8_t x_470; 
x_470 = lean_ctor_get_uint8(x_466, sizeof(void*)*4);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; lean_object* x_484; 
x_471 = lean_ctor_get(x_424, 1);
lean_inc(x_471);
x_472 = lean_ctor_get(x_424, 2);
lean_inc(x_472);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_473 = x_424;
} else {
 lean_dec_ref(x_424);
 x_473 = lean_box(0);
}
x_474 = lean_ctor_get(x_466, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_466, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_466, 2);
lean_inc(x_476);
x_477 = lean_ctor_get(x_466, 3);
lean_inc(x_477);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 lean_ctor_release(x_466, 2);
 lean_ctor_release(x_466, 3);
 x_478 = x_466;
} else {
 lean_dec_ref(x_466);
 x_478 = lean_box(0);
}
x_479 = 1;
lean_inc(x_426);
if (lean_is_scalar(x_478)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_478;
}
lean_ctor_set(x_480, 0, x_342);
lean_ctor_set(x_480, 1, x_343);
lean_ctor_set(x_480, 2, x_344);
lean_ctor_set(x_480, 3, x_426);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_481 = x_426;
} else {
 lean_dec_ref(x_426);
 x_481 = lean_box(0);
}
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_479);
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(1, 4, 1);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_474);
lean_ctor_set(x_482, 1, x_475);
lean_ctor_set(x_482, 2, x_476);
lean_ctor_set(x_482, 3, x_477);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_479);
x_483 = 0;
if (lean_is_scalar(x_473)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_473;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_471);
lean_ctor_set(x_484, 2, x_472);
lean_ctor_set(x_484, 3, x_482);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_483);
return x_484;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; lean_object* x_496; 
x_485 = lean_ctor_get(x_424, 1);
lean_inc(x_485);
x_486 = lean_ctor_get(x_424, 2);
lean_inc(x_486);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_487 = x_424;
} else {
 lean_dec_ref(x_424);
 x_487 = lean_box(0);
}
x_488 = lean_ctor_get(x_426, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_426, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_426, 2);
lean_inc(x_490);
x_491 = lean_ctor_get(x_426, 3);
lean_inc(x_491);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_492 = x_426;
} else {
 lean_dec_ref(x_426);
 x_492 = lean_box(0);
}
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(1, 4, 1);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_488);
lean_ctor_set(x_493, 1, x_489);
lean_ctor_set(x_493, 2, x_490);
lean_ctor_set(x_493, 3, x_491);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_470);
if (lean_is_scalar(x_487)) {
 x_494 = lean_alloc_ctor(1, 4, 1);
} else {
 x_494 = x_487;
}
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_485);
lean_ctor_set(x_494, 2, x_486);
lean_ctor_set(x_494, 3, x_466);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_425);
x_495 = 1;
x_496 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_496, 0, x_342);
lean_ctor_set(x_496, 1, x_343);
lean_ctor_set(x_496, 2, x_344);
lean_ctor_set(x_496, 3, x_494);
lean_ctor_set_uint8(x_496, sizeof(void*)*4, x_495);
return x_496;
}
}
}
}
}
else
{
uint8_t x_497; lean_object* x_498; 
x_497 = 1;
x_498 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_498, 0, x_342);
lean_ctor_set(x_498, 1, x_343);
lean_ctor_set(x_498, 2, x_344);
lean_ctor_set(x_498, 3, x_424);
lean_ctor_set_uint8(x_498, sizeof(void*)*4, x_497);
return x_498;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__6___rarg(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at_Lean_Parser_TokenMap_insert___spec__7___rarg(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__2___rarg(x_1, x_2, x_6);
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
x_10 = l_Lean_RBNode_insert___at_Lean_Parser_TokenMap_insert___spec__5___rarg(x_1, x_2, x_9);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Parser_TokenMap_insert___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_TokenMap_instForInProdNameList___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_TokenMap_instForInProdNameList___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_TokenMap_instForInProdNameList___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProd___boxed), 5, 4);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
lean_closure_set(x_2, 3, lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_TokenMap_instForInProdNameList___closed__2;
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___rarg___closed__1;
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
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8964_(uint8_t x_1, uint8_t x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8964____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8964_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_instBEqLeadingIdentBehavior___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_beqLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8964____boxed), 2, 0);
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
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Parser.LeadingIdentBehavior.default", 40, 40);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__3;
x_2 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__4;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_incQuotDepth___closed__1;
x_2 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__6;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Parser.LeadingIdentBehavior.symbol", 39, 39);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__3;
x_2 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__9;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__11() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__10;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_incQuotDepth___closed__1;
x_2 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__9;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__13() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__12;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Parser.LeadingIdentBehavior.both", 37, 37);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__14;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__3;
x_2 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__15;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__17() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__16;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_incQuotDepth___closed__1;
x_2 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__15;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__19() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__18;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982_(uint8_t x_1, lean_object* x_2) {
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
x_5 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__5;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__7;
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
x_11 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__11;
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__13;
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
x_17 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__17;
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__19;
x_20 = l_Repr_addAppParen(x_19, x_2);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_instReprLeadingIdentBehavior___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____boxed), 2, 0);
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
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_instInhabitedParserCategory___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_instInhabitedParserCategory___closed__2;
x_3 = l_Lean_Parser_instInhabitedPrattParsingTables___closed__1;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instInhabitedParserCategory___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg___boxed), 2, 0);
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
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg(x_1, x_24);
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
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_dec(x_15);
x_30 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg(x_1, x_29);
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
x_39 = l_Lean_Name_str___override(x_38, x_37);
x_40 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg(x_1, x_39);
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
x_46 = l_Lean_Name_str___override(x_45, x_44);
x_47 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg(x_1, x_46);
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
x_54 = l_Lean_Parser_identFn___closed__1;
x_55 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg(x_1, x_54);
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
x_59 = l_Lean_Parser_identFn___closed__1;
x_60 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg(x_1, x_59);
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
x_68 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg(x_1, x_67);
lean_dec(x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_Lean_Parser_identFn___closed__1;
x_70 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg(x_1, x_69);
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
x_76 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg(x_1, x_75);
lean_dec(x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = l_Lean_Parser_identFn___closed__1;
x_78 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg(x_1, x_77);
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
x_88 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg(x_1, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_87);
x_89 = l_Lean_Parser_identFn___closed__1;
x_90 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg(x_1, x_89);
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
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_88, 0);
lean_inc(x_93);
lean_dec(x_88);
x_94 = l_Lean_Parser_identFn___closed__1;
x_95 = lean_name_eq(x_87, x_94);
lean_dec(x_87);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg(x_1, x_94);
if (lean_obj_tag(x_96) == 0)
{
lean_ctor_set(x_5, 1, x_93);
return x_5;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l_List_appendTR___rarg(x_93, x_97);
lean_ctor_set(x_5, 1, x_98);
return x_5;
}
}
else
{
lean_ctor_set(x_5, 1, x_93);
return x_5;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_5, 0);
lean_inc(x_99);
lean_dec(x_5);
x_100 = lean_ctor_get(x_15, 2);
lean_inc(x_100);
lean_dec(x_15);
x_101 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg(x_1, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_100);
x_102 = l_Lean_Parser_identFn___closed__1;
x_103 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg(x_1, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_99);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_103, 0);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_99);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_101, 0);
lean_inc(x_108);
lean_dec(x_101);
x_109 = l_Lean_Parser_identFn___closed__1;
x_110 = lean_name_eq(x_100, x_109);
lean_dec(x_100);
if (x_110 == 0)
{
lean_object* x_111; 
x_111 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg(x_1, x_109);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_99);
lean_ctor_set(x_112, 1, x_108);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l_List_appendTR___rarg(x_108, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_99);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_99);
lean_ctor_set(x_116, 1, x_108);
return x_116;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__2___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__3___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__4___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__5___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__6___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__7___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Parser_indexed___spec__8___rarg(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9445____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_whitespace(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9445____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9445____lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9445_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9445____closed__1;
x_3 = lean_st_mk_ref(x_2, x_1);
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
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9445____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9445____lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9471____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_categoryParserFnRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9471____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9471____lambda__1___closed__1;
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
static lean_object* _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9471____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9471____lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9471_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9471____closed__1;
x_4 = 2;
x_5 = l_Lean_registerEnvExtension___rarg(x_3, x_2, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_categoryParserFn___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_instInhabitedParserFn___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_categoryParserFn___lambda__1___closed__1;
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_categoryParserFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFn___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_categoryParserFn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_categoryParserFn___closed__1;
x_2 = lean_alloc_closure((void*)(l_Pi_instInhabited___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_categoryParserFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_categoryParserFnExtension;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Parser_categoryParserFnExtension;
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_8 = l_Lean_Parser_categoryParserFn___closed__2;
x_9 = l_Lean_Parser_categoryParserFn___closed__3;
x_10 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___rarg(x_8, x_9, x_5, x_7);
x_11 = lean_apply_3(x_10, x_1, x_2, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_categoryParserFn___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_adaptCacheableContextFn(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
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
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_categoryParser___lambda__1), 2, 1);
lean_closure_set(x_3, 0, x_2);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFn), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_categoryParser___elambda__1), 4, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_5);
x_7 = l_Lean_Parser_errorAtSavedPos___closed__2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Parser_termParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_termParser___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_termParser___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
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
static lean_object* _init_l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkNoImmediateColon", 21, 21);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Fail if previous token is immediately followed by ':'. ", 55, 55);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_checkNoImmediateColon___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected ':'", 14, 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_Parser_SyntaxStack_back(x_3);
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
x_10 = lean_string_utf8_get_fast(x_7, x_8);
lean_dec(x_8);
x_11 = 58;
x_12 = lean_uint32_dec_eq(x_10, x_11);
if (x_12 == 0)
{
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_box(0);
x_14 = l_Lean_Parser_checkNoImmediateColon___elambda__1___closed__1;
x_15 = 1;
x_16 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_14, x_13, x_15);
return x_16;
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
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_2(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_5, 4);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 2);
lean_dec(x_12);
lean_ctor_set(x_9, 2, x_1);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_1);
lean_ctor_set(x_6, 0, x_15);
return x_5;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_ctor_get(x_5, 3);
x_21 = lean_ctor_get(x_5, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 x_24 = x_16;
} else {
 lean_dec_ref(x_16);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 3, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_1);
lean_ctor_set(x_6, 0, x_25);
x_26 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_19);
lean_ctor_set(x_26, 3, x_20);
lean_ctor_set(x_26, 4, x_6);
lean_ctor_set(x_26, 5, x_21);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
x_28 = lean_ctor_get(x_5, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_5, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_5, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_5, 5);
lean_inc(x_32);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 x_33 = x_5;
} else {
 lean_dec_ref(x_5);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 x_36 = x_27;
} else {
 lean_dec_ref(x_27);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 3, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_1);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
if (lean_is_scalar(x_33)) {
 x_39 = lean_alloc_ctor(0, 6, 0);
} else {
 x_39 = x_33;
}
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_29);
lean_ctor_set(x_39, 2, x_30);
lean_ctor_set(x_39, 3, x_31);
lean_ctor_set(x_39, 4, x_38);
lean_ctor_set(x_39, 5, x_32);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_setExpectedFn(x_1, x_2, x_3, x_4);
return x_5;
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
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_setExpected___elambda__1), 4, 2);
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
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_setExpected___elambda__1), 4, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Parser_pushNone___elambda__1___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_pushNone___elambda__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Lean_Parser_optionalFn___closed__2;
x_3 = l_Lean_Parser_pushNone___elambda__1___rarg___closed__1;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___elambda__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_pushNone___elambda__1___rarg___closed__2;
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
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("antiquotNestedExpr", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_antiquotNestedExpr___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_antiquotNestedExpr___closed__3;
x_2 = l_Lean_Parser_symbolNoAntiquot(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Parser_termParser(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_antiquotNestedExpr___closed__5;
x_2 = l_Lean_Parser_decQuotDepth(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_dbgTraceStateFn___closed__8;
x_2 = l_Lean_Parser_symbolNoAntiquot(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr___closed__6;
x_2 = l_Lean_Parser_antiquotNestedExpr___closed__7;
x_3 = l_Lean_Parser_andthen(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr___closed__4;
x_2 = l_Lean_Parser_antiquotNestedExpr___closed__8;
x_3 = l_Lean_Parser_andthen(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotNestedExpr___closed__2;
x_2 = l_Lean_Parser_antiquotNestedExpr___closed__9;
x_3 = l_Lean_Parser_node(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_antiquotNestedExpr___closed__10;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_antiquotExpr___closed__1;
x_2 = l_Lean_Parser_symbolNoAntiquot(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_antiquotExpr___closed__2;
x_2 = l_Lean_Parser_antiquotNestedExpr;
x_3 = l_Lean_Parser_orelse(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_identNoAntiquot;
x_2 = l_Lean_Parser_antiquotExpr___closed__3;
x_3 = l_Lean_Parser_orelse(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_antiquotExpr___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("token_antiquot", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_tokenAntiquotFn___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = l_Lean_Parser_tokenAntiquotFn___lambda__1___closed__2;
x_7 = l_Lean_Parser_ParserState_mkNode(x_2, x_6, x_5);
lean_dec(x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no space before", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__1;
x_2 = l_Lean_Parser_checkNoWsBefore(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("%", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__3;
x_2 = l_Lean_Parser_symbolNoAntiquot(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("$", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__5;
x_2 = l_Lean_Parser_symbolNoAntiquot(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__2;
x_2 = l_Lean_Parser_antiquotExpr;
x_3 = l_Lean_Parser_andthen(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__6;
x_2 = l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__7;
x_3 = l_Lean_Parser_andthen(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__4;
x_2 = l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__8;
x_3 = l_Lean_Parser_andthen(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__2;
x_2 = l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__9;
x_3 = l_Lean_Parser_andthen(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lean_Parser_ParserState_stackSize(x_1);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__10;
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_apply_2(x_7, x_2, x_1);
x_9 = lean_ctor_get(x_8, 4);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Parser_ParserState_restore(x_8, x_4, x_5);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = l_Lean_Parser_tokenAntiquotFn___lambda__1(x_4, x_8, x_13);
lean_dec(x_4);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
x_4 = lean_box(0);
x_5 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_Parser_tokenAntiquotFn___lambda__2(x_2, x_1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_tokenAntiquotFn___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_tokenAntiquotFn___lambda__2(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; uint32_t x_9; uint8_t x_10; 
lean_inc(x_2);
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_string_utf8_get(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
x_9 = 37;
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_11; 
x_11 = l_Lean_Parser_tokenAntiquotFn(x_2, x_4);
return x_11;
}
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
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquot___elambda__1), 3, 1);
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
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquot___elambda__1), 3, 1);
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
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Parser_symbolNoAntiquot(x_1);
x_3 = l_Lean_Parser_tokenWithAntiquot(x_2);
return x_3;
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
static lean_object* _init_l_Lean_Parser_instCoeStringParser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_symbol___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_instCoeStringParser() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_instCoeStringParser___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_nonReservedSymbolNoAntiquot(x_1, x_2);
x_4 = l_Lean_Parser_tokenWithAntiquot(x_3);
return x_4;
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
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parser_unicodeSymbolNoAntiquot(x_1, x_2);
x_4 = l_Lean_Parser_tokenWithAntiquot(x_3);
return x_4;
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
static lean_object* _init_l___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkAntiquot", 10, 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Define parser for `$e` (if `anonymous == true`) and `$e:name`.\n`kind` is embedded in the antiquotation's kind, and checked at syntax `match` unless `isPseudoKind` is true.\nAntiquotations can be escaped as in `$$e`, which produces the syntax tree for `$e`. ", 256, 256);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_mkAntiquot_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("antiquot", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_mkAntiquot___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("antiquotName", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_mkAntiquot___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no space before ':", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot___closed__6;
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__5;
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_dbgTraceStateFn___closed__1;
x_2 = l_Lean_Parser_checkNoWsBefore(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_mkAntiquot___closed__10;
x_2 = l_Lean_Parser_mkAntiquot___closed__8;
x_3 = l_Lean_Parser_andthen(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot___closed__11;
x_2 = l_Lean_Parser_manyNoAntiquot(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no space before spliced term", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquot___closed__13;
x_2 = l_Lean_Parser_checkNoWsBefore(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_checkNoImmediateColon;
x_2 = l_Lean_Parser_pushNone;
x_3 = l_Lean_Parser_andthen(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pseudo", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_mkAntiquot___closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = l_Lean_Parser_mkAntiquot___closed__5;
x_6 = lean_string_append(x_5, x_1);
x_7 = l_Lean_Parser_chFn___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Lean_Parser_checkNoWsBefore(x_8);
x_10 = 0;
x_11 = l_Lean_Parser_nonReservedSymbol(x_1, x_10);
x_12 = l_Lean_Parser_mkAntiquot___closed__7;
x_13 = l_Lean_Parser_andthen(x_12, x_11);
x_14 = l_Lean_Parser_andthen(x_9, x_13);
x_15 = l_Lean_Parser_mkAntiquot___closed__4;
x_16 = l_Lean_Parser_node(x_15, x_14);
if (x_4 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_box(0);
x_18 = l_Lean_Name_append(x_2, x_17);
x_19 = l_Lean_Parser_mkAntiquot___closed__2;
x_20 = l_Lean_Name_append(x_18, x_19);
if (x_3 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = l_Lean_Parser_antiquotExpr;
x_22 = l_Lean_Parser_andthen(x_21, x_16);
x_23 = l_Lean_Parser_mkAntiquot___closed__14;
x_24 = l_Lean_Parser_andthen(x_23, x_22);
x_25 = l_Lean_Parser_mkAntiquot___closed__12;
x_26 = l_Lean_Parser_andthen(x_25, x_24);
x_27 = l_Lean_Parser_mkAntiquot___closed__9;
x_28 = l_Lean_Parser_andthen(x_27, x_26);
x_29 = l_Lean_Parser_atomic(x_28);
x_30 = l_Lean_Parser_maxPrec;
x_31 = l_Lean_Parser_leadingNode(x_20, x_30, x_29);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_32 = l_Lean_Parser_mkAntiquot___closed__15;
x_33 = l_Lean_Parser_orelse(x_16, x_32);
x_34 = l_Lean_Parser_antiquotExpr;
x_35 = l_Lean_Parser_andthen(x_34, x_33);
x_36 = l_Lean_Parser_mkAntiquot___closed__14;
x_37 = l_Lean_Parser_andthen(x_36, x_35);
x_38 = l_Lean_Parser_mkAntiquot___closed__12;
x_39 = l_Lean_Parser_andthen(x_38, x_37);
x_40 = l_Lean_Parser_mkAntiquot___closed__9;
x_41 = l_Lean_Parser_andthen(x_40, x_39);
x_42 = l_Lean_Parser_atomic(x_41);
x_43 = l_Lean_Parser_maxPrec;
x_44 = l_Lean_Parser_leadingNode(x_20, x_43, x_42);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = l_Lean_Parser_mkAntiquot___closed__17;
x_46 = l_Lean_Name_append(x_2, x_45);
x_47 = l_Lean_Parser_mkAntiquot___closed__2;
x_48 = l_Lean_Name_append(x_46, x_47);
if (x_3 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_49 = l_Lean_Parser_antiquotExpr;
x_50 = l_Lean_Parser_andthen(x_49, x_16);
x_51 = l_Lean_Parser_mkAntiquot___closed__14;
x_52 = l_Lean_Parser_andthen(x_51, x_50);
x_53 = l_Lean_Parser_mkAntiquot___closed__12;
x_54 = l_Lean_Parser_andthen(x_53, x_52);
x_55 = l_Lean_Parser_mkAntiquot___closed__9;
x_56 = l_Lean_Parser_andthen(x_55, x_54);
x_57 = l_Lean_Parser_atomic(x_56);
x_58 = l_Lean_Parser_maxPrec;
x_59 = l_Lean_Parser_leadingNode(x_48, x_58, x_57);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = l_Lean_Parser_mkAntiquot___closed__15;
x_61 = l_Lean_Parser_orelse(x_16, x_60);
x_62 = l_Lean_Parser_antiquotExpr;
x_63 = l_Lean_Parser_andthen(x_62, x_61);
x_64 = l_Lean_Parser_mkAntiquot___closed__14;
x_65 = l_Lean_Parser_andthen(x_64, x_63);
x_66 = l_Lean_Parser_mkAntiquot___closed__12;
x_67 = l_Lean_Parser_andthen(x_66, x_65);
x_68 = l_Lean_Parser_mkAntiquot___closed__9;
x_69 = l_Lean_Parser_andthen(x_68, x_67);
x_70 = l_Lean_Parser_atomic(x_69);
x_71 = l_Lean_Parser_maxPrec;
x_72 = l_Lean_Parser_leadingNode(x_48, x_71, x_70);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_string_utf8_get(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
x_10 = 36;
x_11 = lean_uint32_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = lean_apply_2(x_2, x_4, x_5);
return x_12;
}
else
{
if (x_3 == 0)
{
uint8_t x_13; lean_object* x_14; 
x_13 = 1;
x_14 = l_Lean_Parser_orelseFnCore(x_1, x_2, x_13, x_4, x_5);
return x_14;
}
else
{
uint8_t x_15; lean_object* x_16; 
x_15 = 0;
x_16 = l_Lean_Parser_orelseFnCore(x_1, x_2, x_15, x_4, x_5);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Parser_withAntiquotFn(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withAntiquot", 12, 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Optimized version of `mkAntiquot ... <|> p`. ", 45, 45);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withAntiquot_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = l_Lean_Parser_withAntiquotFn(x_1, x_2, x_5, x_3, x_4);
return x_6;
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
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquot___elambda__1), 4, 2);
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
static lean_object* _init_l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkAntiquotSplice", 16, 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parse `$[p]suffix`, e.g. `$[p],*`. ", 35, 35);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("antiquot_scope", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_mkAntiquotSplice___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquotSplice___closed__3;
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_mkAntiquotSplice___closed__5;
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_4 = l_Lean_Parser_mkAntiquotSplice___closed__2;
x_5 = l_Lean_Name_append(x_1, x_4);
x_6 = l_Lean_Parser_optionalFn___closed__2;
x_7 = l_Lean_Parser_node(x_6, x_2);
x_8 = l_Lean_Parser_mkAntiquotSplice___closed__6;
x_9 = l_Lean_Parser_andthen(x_8, x_3);
x_10 = l_Lean_Parser_andthen(x_7, x_9);
x_11 = l_Lean_Parser_mkAntiquotSplice___closed__4;
x_12 = l_Lean_Parser_andthen(x_11, x_10);
x_13 = l_Lean_Parser_mkAntiquot___closed__14;
x_14 = l_Lean_Parser_andthen(x_13, x_12);
x_15 = l_Lean_Parser_mkAntiquot___closed__12;
x_16 = l_Lean_Parser_andthen(x_15, x_14);
x_17 = l_Lean_Parser_mkAntiquot___closed__9;
x_18 = l_Lean_Parser_andthen(x_17, x_16);
x_19 = l_Lean_Parser_atomic(x_18);
x_20 = l_Lean_Parser_maxPrec;
x_21 = l_Lean_Parser_leadingNode(x_5, x_20, x_19);
return x_21;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("antiquot_suffix_splice", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__2;
x_5 = l_Lean_Name_append(x_1, x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = l_Lean_Parser_SyntaxStack_size(x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Parser_ParserState_mkNode(x_2, x_5, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = l_Lean_Parser_ParserState_stackSize(x_4);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_apply_2(x_2, x_3, x_4);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = l_Lean_Parser_ParserState_restore(x_7, x_5, x_6);
lean_dec(x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
x_12 = lean_box(0);
x_13 = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1(x_1, x_7, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withAntiquotSuffixSplice", 24, 24);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1;
x_2 = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parse `suffix` after an antiquotation, e.g. `$x,*`, and put both into a new node. ", 82, 82);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2;
x_3 = l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__3;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_4);
x_7 = lean_apply_2(x_6, x_4, x_5);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = l_Lean_Parser_SyntaxStack_back(x_11);
lean_dec(x_11);
x_13 = l_Lean_Syntax_isAntiquots(x_12);
if (x_13 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(x_1, x_14, x_4, x_7);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = l_Lean_Parser_andthenInfo(x_4, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSuffixSplice___elambda__1), 5, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
x_4 = l_Lean_Parser_withoutInfo(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Parser_mkAntiquotSplice(x_1, x_4, x_3);
x_6 = l_Lean_Parser_withAntiquotSuffixSplice(x_1, x_2, x_3);
x_7 = l_Lean_Parser_withAntiquot(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = 0;
lean_inc(x_2);
x_6 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_4, x_5);
x_7 = l_Lean_Parser_node(x_2, x_3);
x_8 = l_Lean_Parser_withAntiquot(x_6, x_7);
return x_8;
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
x_1 = lean_mk_string_unchecked("sepBy", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_sepByElemParser___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_sepByElemParser___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_sepByElemParser___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("*", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_string_utf8_byte_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_2, x_3, x_4);
x_6 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_2, x_5, x_3);
x_7 = lean_string_utf8_extract(x_2, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_8 = l_Lean_Parser_sepByElemParser___closed__3;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Lean_Parser_symbol(x_9);
lean_dec(x_9);
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
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parser_sepByElemParser(x_1, x_2);
x_6 = l_Lean_Parser_sepByNoAntiquot(x_5, x_3, x_4);
return x_6;
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
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parser_sepByElemParser(x_1, x_2);
x_6 = l_Lean_Parser_sepBy1NoAntiquot(x_5, x_3, x_4);
return x_6;
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lean_Parser_ParserState_stackSize(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
x_6 = lean_nat_dec_eq(x_3, x_5);
lean_dec(x_5);
lean_dec(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Parser_optionalFn___closed__2;
x_8 = l_Lean_Parser_ParserState_mkNode(x_1, x_7, x_2);
return x_8;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(x_1, x_2);
lean_dec(x_2);
return x_3;
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
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_9);
x_13 = 1;
x_14 = l_Lean_Parser_identEqFn___closed__2;
x_15 = l_Lean_Name_toString(x_6, x_13, x_14);
x_16 = lean_box(0);
lean_inc(x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Parser_tokenFn(x_17, x_3, x_4);
x_19 = lean_ctor_get(x_18, 4);
lean_inc(x_19);
x_20 = lean_box(0);
x_21 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_15);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Parser_ParserState_mkUnexpectedTokenError(x_18, x_15, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = l_Lean_Parser_ParserState_stackSize(x_5);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_inc(x_4);
x_8 = l_Lean_Parser_indexed___rarg(x_7, x_4, x_5, x_3);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 4);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Parser_leadingParserAux___lambda__2(x_2, x_10, x_4, x_9, x_6, x_1, x_14);
lean_dec(x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_leadingParserAux___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Parser_leadingParserAux___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_box(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Parser_leadingParserAux___boxed), 5, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_7);
x_9 = 1;
x_10 = l_Lean_Parser_withAntiquotFn(x_4, x_8, x_9, x_5, x_6);
return x_10;
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
x_9 = l_Lean_Parser_SyntaxStack_back(x_8);
lean_dec(x_8);
x_10 = l_Lean_Parser_ParserState_popSyntax(x_1);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_2);
x_11 = l_Lean_Parser_trailingLoopStep(x_2, x_9, x_3, x_4, x_10);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_12, x_13);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = l_Lean_Parser_ParserState_stackSize(x_3);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = 0;
lean_inc(x_2);
x_8 = l_Lean_Parser_indexed___rarg(x_6, x_2, x_3, x_7);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 4);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Parser_ParserState_restore(x_9, x_4, x_5);
lean_dec(x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_Parser_trailingLoop___lambda__3(x_9, x_1, x_10, x_2, x_5, x_4, x_15);
lean_dec(x_4);
return x_16;
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
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_5);
lean_inc(x_2);
x_7 = l_Lean_Parser_leadingParser(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Parser_ParserState_hasError___spec__1(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_11; 
x_11 = l_Lean_Parser_trailingLoop(x_2, x_5, x_7);
return x_11;
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
x_1 = lean_mk_string_unchecked("field index", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdxFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fieldIdx", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdxFn___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_fieldIdxFn___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdxFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_3 = l_Lean_Parser_ParserState_stackSize(x_2);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_string_utf8_get(x_6, x_4);
lean_dec(x_6);
x_8 = 48;
x_9 = lean_uint32_dec_le(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_3);
x_11 = l_Lean_Parser_fieldIdxFn___closed__1;
x_12 = l_Lean_Parser_ParserState_mkErrorAt(x_2, x_11, x_4, x_10);
lean_dec(x_10);
return x_12;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 57;
x_14 = lean_uint32_dec_le(x_7, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_3);
x_16 = l_Lean_Parser_fieldIdxFn___closed__1;
x_17 = l_Lean_Parser_ParserState_mkErrorAt(x_2, x_16, x_4, x_15);
lean_dec(x_15);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_uint32_dec_eq(x_7, x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_19 = l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1;
x_20 = l_Lean_Parser_takeWhileFn(x_19, x_1, x_2);
x_21 = l_Lean_Parser_fieldIdxFn___closed__3;
x_22 = l_Lean_Parser_mkNodeToken(x_21, x_4, x_1, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_3);
x_24 = l_Lean_Parser_fieldIdxFn___closed__1;
x_25 = l_Lean_Parser_ParserState_mkErrorAt(x_2, x_24, x_4, x_23);
lean_dec(x_23);
return x_25;
}
}
}
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_fieldIdxFn___closed__2;
x_2 = l_Lean_Parser_fieldIdxFn___closed__3;
x_3 = 1;
x_4 = 0;
x_5 = l_Lean_Parser_mkAntiquot(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_fieldIdxFn___closed__2;
x_2 = l_Lean_Parser_mkAtomicInfo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_fieldIdxFn), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_fieldIdx___closed__2;
x_2 = l_Lean_Parser_fieldIdx___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_fieldIdx___closed__1;
x_2 = l_Lean_Parser_fieldIdx___closed__4;
x_3 = l_Lean_Parser_withAntiquot(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_fieldIdx___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___elambda__1___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_skip___elambda__1___rarg___boxed), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_skip___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_skip___elambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_skip___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_epsilonInfo;
x_2 = l_Lean_Parser_skip___closed__1;
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
x_1 = l_Lean_Parser_skip___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___elambda__1___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_skip___elambda__1___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_skip___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg(x_2, lean_box(0), x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_array_uget(x_4, x_5);
lean_inc(x_3);
x_11 = lean_apply_2(x_3, x_10, x_7);
x_12 = lean_box_usize(x_5);
x_13 = lean_box_usize(x_6);
x_14 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_13);
x_15 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_11, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_apply_2(x_17, lean_box(0), x_7);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_Syntax_getArgs(x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_5);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_7, x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_2(x_15, lean_box(0), x_5);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg(x_1, lean_box(0), x_4, x_6, x_17, x_18, x_5);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_foldArgsM___rarg___boxed), 5, 0);
return x_2;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgsM___spec__1___rarg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_foldArgsM___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__2___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_7, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__2___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at_Lean_Syntax_foldArgs___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__2___rarg(x_2, x_4, x_9, x_10, x_3);
lean_dec(x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at_Lean_Syntax_foldArgs___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_foldArgsM___at_Lean_Syntax_foldArgs___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_foldArgsM___at_Lean_Syntax_foldArgs___spec__1___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_foldArgs___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_foldArgs___spec__2___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at_Lean_Syntax_foldArgs___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_foldArgsM___at_Lean_Syntax_foldArgs___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_foldArgs___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__2___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__2___rarg(x_2, lean_box(0), x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_array_uget(x_4, x_5);
lean_inc(x_3);
x_11 = lean_apply_2(x_3, x_10, x_7);
x_12 = lean_box_usize(x_5);
x_13 = lean_box_usize(x_6);
x_14 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__2___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_13);
x_15 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_11, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_apply_2(x_17, lean_box(0), x_7);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__2___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at_Lean_Syntax_forArgsM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_Syntax_getArgs(x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_5);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_7, x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_2(x_15, lean_box(0), x_5);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__2___rarg(x_1, lean_box(0), x_4, x_6, x_17, x_18, x_5);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at_Lean_Syntax_forArgsM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_foldArgsM___at_Lean_Syntax_forArgsM___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_Syntax_forArgsM___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Syntax_foldArgsM___at_Lean_Syntax_forArgsM___spec__1___rarg(x_1, lean_box(0), x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_forArgsM___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__2___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_forArgsM___spec__2___rarg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at_Lean_Syntax_forArgsM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_foldArgsM___at_Lean_Syntax_forArgsM___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_forArgsM___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_forArgsM___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Lean_Parser_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Lean_Parser_dbgTraceStateFn___closed__8 = _init_l_Lean_Parser_dbgTraceStateFn___closed__8();
lean_mark_persistent(l_Lean_Parser_dbgTraceStateFn___closed__8);
l_Lean_Parser_epsilonInfo___closed__1 = _init_l_Lean_Parser_epsilonInfo___closed__1();
lean_mark_persistent(l_Lean_Parser_epsilonInfo___closed__1);
l_Lean_Parser_epsilonInfo___closed__2 = _init_l_Lean_Parser_epsilonInfo___closed__2();
lean_mark_persistent(l_Lean_Parser_epsilonInfo___closed__2);
l_Lean_Parser_epsilonInfo___closed__3 = _init_l_Lean_Parser_epsilonInfo___closed__3();
lean_mark_persistent(l_Lean_Parser_epsilonInfo___closed__3);
l_Lean_Parser_epsilonInfo = _init_l_Lean_Parser_epsilonInfo();
lean_mark_persistent(l_Lean_Parser_epsilonInfo);
l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__1);
l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__2);
l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__3);
l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__4 = _init_l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__4);
l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__5 = _init_l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Parser_errorAtSavedPos_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_errorAtSavedPos___closed__1 = _init_l_Lean_Parser_errorAtSavedPos___closed__1();
lean_mark_persistent(l_Lean_Parser_errorAtSavedPos___closed__1);
l_Lean_Parser_errorAtSavedPos___closed__2 = _init_l_Lean_Parser_errorAtSavedPos___closed__2();
lean_mark_persistent(l_Lean_Parser_errorAtSavedPos___closed__2);
l_Lean_Parser_checkPrecFn___closed__1 = _init_l_Lean_Parser_checkPrecFn___closed__1();
lean_mark_persistent(l_Lean_Parser_checkPrecFn___closed__1);
l_Lean_Parser_incQuotDepth___closed__1 = _init_l_Lean_Parser_incQuotDepth___closed__1();
lean_mark_persistent(l_Lean_Parser_incQuotDepth___closed__1);
l_Lean_Parser_decQuotDepth___closed__1 = _init_l_Lean_Parser_decQuotDepth___closed__1();
lean_mark_persistent(l_Lean_Parser_decQuotDepth___closed__1);
l_Lean_Parser_suppressInsideQuot___closed__1 = _init_l_Lean_Parser_suppressInsideQuot___closed__1();
lean_mark_persistent(l_Lean_Parser_suppressInsideQuot___closed__1);
l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___rarg___closed__1 = _init_l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_OrElseOnAntiquotBehavior_noConfusion___rarg___closed__1);
l_Lean_Parser_instBEqOrElseOnAntiquotBehavior___closed__1 = _init_l_Lean_Parser_instBEqOrElseOnAntiquotBehavior___closed__1();
lean_mark_persistent(l_Lean_Parser_instBEqOrElseOnAntiquotBehavior___closed__1);
l_Lean_Parser_instBEqOrElseOnAntiquotBehavior = _init_l_Lean_Parser_instBEqOrElseOnAntiquotBehavior();
lean_mark_persistent(l_Lean_Parser_instBEqOrElseOnAntiquotBehavior);
l_Lean_Parser_orelseFnCore___lambda__1___closed__1 = _init_l_Lean_Parser_orelseFnCore___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_orelseFnCore___lambda__1___closed__1);
l_Lean_Parser_orelseFnCore___lambda__1___closed__2 = _init_l_Lean_Parser_orelseFnCore___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_orelseFnCore___lambda__1___closed__2);
l___regBuiltin_Lean_Parser_orelse_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_orelse_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_orelse_docString__1___closed__1);
l___regBuiltin_Lean_Parser_orelse_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_orelse_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_orelse_docString__1___closed__2);
l___regBuiltin_Lean_Parser_orelse_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_orelse_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_orelse_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_orelse_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Parser_atomic_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_atomic_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_atomic_docString__1___closed__1);
l___regBuiltin_Lean_Parser_atomic_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_atomic_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_atomic_docString__1___closed__2);
l___regBuiltin_Lean_Parser_atomic_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_atomic_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_atomic_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_atomic_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_instBEqRecoveryContext___closed__1 = _init_l_Lean_Parser_instBEqRecoveryContext___closed__1();
lean_mark_persistent(l_Lean_Parser_instBEqRecoveryContext___closed__1);
l_Lean_Parser_instBEqRecoveryContext = _init_l_Lean_Parser_instBEqRecoveryContext();
lean_mark_persistent(l_Lean_Parser_instBEqRecoveryContext);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__1 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__1();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__1);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__2 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__2();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__2);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__3 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__3();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__3);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__4 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__4();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__4);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__5 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__5();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__5);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__6 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__6();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__6);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__7 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__7();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__7);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__8 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__8();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__8);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__9 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__9();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__9);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__10 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__10();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__10);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__11 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__11();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__11);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__12 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__12();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__12);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__13 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__13();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__13);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__14 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__14();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__14);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__15 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__15();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__15);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__16 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__16();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__16);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__17 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__17();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__17);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__18 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__18();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__18);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__19 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__19();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__19);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__20 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__20();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprRecoveryContext____x40_Lean_Parser_Basic___hyg_1474____closed__20);
l_Lean_Parser_instReprRecoveryContext___closed__1 = _init_l_Lean_Parser_instReprRecoveryContext___closed__1();
lean_mark_persistent(l_Lean_Parser_instReprRecoveryContext___closed__1);
l_Lean_Parser_instReprRecoveryContext = _init_l_Lean_Parser_instReprRecoveryContext();
lean_mark_persistent(l_Lean_Parser_instReprRecoveryContext);
l___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1);
l___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2);
l___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_recover_x27_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Parser_recover_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_recover_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_recover_docString__1___closed__1);
l___regBuiltin_Lean_Parser_recover_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_recover_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_recover_docString__1___closed__2);
l___regBuiltin_Lean_Parser_recover_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_recover_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_recover_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_recover_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_optionalFn___closed__1 = _init_l_Lean_Parser_optionalFn___closed__1();
lean_mark_persistent(l_Lean_Parser_optionalFn___closed__1);
l_Lean_Parser_optionalFn___closed__2 = _init_l_Lean_Parser_optionalFn___closed__2();
lean_mark_persistent(l_Lean_Parser_optionalFn___closed__2);
l___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1);
l___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2);
l___regBuiltin_Lean_Parser_lookahead_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_lookahead_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_lookahead_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_lookahead_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_notFollowedByFn___closed__1 = _init_l_Lean_Parser_notFollowedByFn___closed__1();
lean_mark_persistent(l_Lean_Parser_notFollowedByFn___closed__1);
l___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1);
l___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2);
l___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_notFollowedBy_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_manyAux___lambda__3___closed__1 = _init_l_Lean_Parser_manyAux___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Parser_manyAux___lambda__3___closed__1);
l_Lean_Parser_many1Unbox___closed__1 = _init_l_Lean_Parser_many1Unbox___closed__1();
lean_mark_persistent(l_Lean_Parser_many1Unbox___closed__1);
l_Lean_Parser_satisfyFn___closed__1 = _init_l_Lean_Parser_satisfyFn___closed__1();
lean_mark_persistent(l_Lean_Parser_satisfyFn___closed__1);
l_Lean_Parser_finishCommentBlock_eoi___closed__1 = _init_l_Lean_Parser_finishCommentBlock_eoi___closed__1();
lean_mark_persistent(l_Lean_Parser_finishCommentBlock_eoi___closed__1);
l_Lean_Parser_whitespace___closed__1 = _init_l_Lean_Parser_whitespace___closed__1();
lean_mark_persistent(l_Lean_Parser_whitespace___closed__1);
l_Lean_Parser_whitespace___closed__2 = _init_l_Lean_Parser_whitespace___closed__2();
lean_mark_persistent(l_Lean_Parser_whitespace___closed__2);
l_Lean_Parser_whitespace___closed__3 = _init_l_Lean_Parser_whitespace___closed__3();
lean_mark_persistent(l_Lean_Parser_whitespace___closed__3);
l_Lean_Parser_whitespace___closed__4 = _init_l_Lean_Parser_whitespace___closed__4();
lean_mark_persistent(l_Lean_Parser_whitespace___closed__4);
l_Lean_Parser_whitespace___boxed__const__1 = _init_l_Lean_Parser_whitespace___boxed__const__1();
lean_mark_persistent(l_Lean_Parser_whitespace___boxed__const__1);
l_Lean_Parser_chFn___closed__1 = _init_l_Lean_Parser_chFn___closed__1();
lean_mark_persistent(l_Lean_Parser_chFn___closed__1);
l_Lean_Parser_hexDigitFn___closed__1 = _init_l_Lean_Parser_hexDigitFn___closed__1();
lean_mark_persistent(l_Lean_Parser_hexDigitFn___closed__1);
l_Lean_Parser_stringGapFn___closed__1 = _init_l_Lean_Parser_stringGapFn___closed__1();
lean_mark_persistent(l_Lean_Parser_stringGapFn___closed__1);
l_Lean_Parser_stringGapFn___closed__2 = _init_l_Lean_Parser_stringGapFn___closed__2();
lean_mark_persistent(l_Lean_Parser_stringGapFn___closed__2);
l_Lean_Parser_quotedCharCoreFn___closed__1 = _init_l_Lean_Parser_quotedCharCoreFn___closed__1();
lean_mark_persistent(l_Lean_Parser_quotedCharCoreFn___closed__1);
l_Lean_Parser_quotedCharCoreFn___closed__2 = _init_l_Lean_Parser_quotedCharCoreFn___closed__2();
lean_mark_persistent(l_Lean_Parser_quotedCharCoreFn___closed__2);
l_Lean_Parser_quotedCharCoreFn___closed__3 = _init_l_Lean_Parser_quotedCharCoreFn___closed__3();
lean_mark_persistent(l_Lean_Parser_quotedCharCoreFn___closed__3);
l_Lean_Parser_quotedCharCoreFn___closed__4 = _init_l_Lean_Parser_quotedCharCoreFn___closed__4();
lean_mark_persistent(l_Lean_Parser_quotedCharCoreFn___closed__4);
l_Lean_Parser_quotedCharFn___closed__1 = _init_l_Lean_Parser_quotedCharFn___closed__1();
lean_mark_persistent(l_Lean_Parser_quotedCharFn___closed__1);
l_Lean_Parser_charLitFnAux___closed__1 = _init_l_Lean_Parser_charLitFnAux___closed__1();
lean_mark_persistent(l_Lean_Parser_charLitFnAux___closed__1);
l_Lean_Parser_charLitFnAux___closed__2 = _init_l_Lean_Parser_charLitFnAux___closed__2();
lean_mark_persistent(l_Lean_Parser_charLitFnAux___closed__2);
l_Lean_Parser_charLitFnAux___closed__3 = _init_l_Lean_Parser_charLitFnAux___closed__3();
lean_mark_persistent(l_Lean_Parser_charLitFnAux___closed__3);
l_Lean_Parser_strLitFnAux___closed__1 = _init_l_Lean_Parser_strLitFnAux___closed__1();
lean_mark_persistent(l_Lean_Parser_strLitFnAux___closed__1);
l_Lean_Parser_strLitFnAux___closed__2 = _init_l_Lean_Parser_strLitFnAux___closed__2();
lean_mark_persistent(l_Lean_Parser_strLitFnAux___closed__2);
l_Lean_Parser_strLitFnAux___closed__3 = _init_l_Lean_Parser_strLitFnAux___closed__3();
lean_mark_persistent(l_Lean_Parser_strLitFnAux___closed__3);
l_Lean_Parser_strLitFnAux___closed__4 = _init_l_Lean_Parser_strLitFnAux___closed__4();
lean_mark_persistent(l_Lean_Parser_strLitFnAux___closed__4);
l_Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__1 = _init_l_Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__1();
lean_mark_persistent(l_Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__1);
l_Lean_Parser_takeDigitsFn___closed__1 = _init_l_Lean_Parser_takeDigitsFn___closed__1();
lean_mark_persistent(l_Lean_Parser_takeDigitsFn___closed__1);
l_Lean_Parser_decimalNumberFn_parseOptExp___closed__1 = _init_l_Lean_Parser_decimalNumberFn_parseOptExp___closed__1();
lean_mark_persistent(l_Lean_Parser_decimalNumberFn_parseOptExp___closed__1);
l_Lean_Parser_decimalNumberFn_parseOptExp___closed__2 = _init_l_Lean_Parser_decimalNumberFn_parseOptExp___closed__2();
lean_mark_persistent(l_Lean_Parser_decimalNumberFn_parseOptExp___closed__2);
l_Lean_Parser_decimalNumberFn_parseOptExp___boxed__const__1 = _init_l_Lean_Parser_decimalNumberFn_parseOptExp___boxed__const__1();
lean_mark_persistent(l_Lean_Parser_decimalNumberFn_parseOptExp___boxed__const__1);
l_Lean_Parser_decimalNumberFn_parseOptExp___boxed__const__2 = _init_l_Lean_Parser_decimalNumberFn_parseOptExp___boxed__const__2();
lean_mark_persistent(l_Lean_Parser_decimalNumberFn_parseOptExp___boxed__const__2);
l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1___boxed__const__1 = _init_l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1___boxed__const__1();
lean_mark_persistent(l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1___boxed__const__1);
l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1___boxed__const__2 = _init_l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1___boxed__const__2();
lean_mark_persistent(l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1___boxed__const__2);
l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1 = _init_l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1();
lean_mark_persistent(l_Lean_Parser_decimalNumberFn_parseOptDot___closed__1);
l_Lean_Parser_decimalNumberFn_parseScientific___closed__1 = _init_l_Lean_Parser_decimalNumberFn_parseScientific___closed__1();
lean_mark_persistent(l_Lean_Parser_decimalNumberFn_parseScientific___closed__1);
l_Lean_Parser_decimalNumberFn_parseScientific___closed__2 = _init_l_Lean_Parser_decimalNumberFn_parseScientific___closed__2();
lean_mark_persistent(l_Lean_Parser_decimalNumberFn_parseScientific___closed__2);
l_Lean_Parser_decimalNumberFn___closed__1 = _init_l_Lean_Parser_decimalNumberFn___closed__1();
lean_mark_persistent(l_Lean_Parser_decimalNumberFn___closed__1);
l_Lean_Parser_decimalNumberFn___closed__2 = _init_l_Lean_Parser_decimalNumberFn___closed__2();
lean_mark_persistent(l_Lean_Parser_decimalNumberFn___closed__2);
l_Lean_Parser_decimalNumberFn___closed__3 = _init_l_Lean_Parser_decimalNumberFn___closed__3();
lean_mark_persistent(l_Lean_Parser_decimalNumberFn___closed__3);
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
l_Lean_Parser_nonReservedSymbolInfo___closed__4 = _init_l_Lean_Parser_nonReservedSymbolInfo___closed__4();
lean_mark_persistent(l_Lean_Parser_nonReservedSymbolInfo___closed__4);
l___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1);
l___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2);
l___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_checkWsBefore_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1);
l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2);
l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1);
l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2);
l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_unicodeSymbolInfo___closed__1 = _init_l_Lean_Parser_unicodeSymbolInfo___closed__1();
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
l_Lean_Parser_nameLitFn___closed__2 = _init_l_Lean_Parser_nameLitFn___closed__2();
lean_mark_persistent(l_Lean_Parser_nameLitFn___closed__2);
l_Lean_Parser_nameLitFn___closed__3 = _init_l_Lean_Parser_nameLitFn___closed__3();
lean_mark_persistent(l_Lean_Parser_nameLitFn___closed__3);
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
l_Lean_Parser_identEqFn___closed__2 = _init_l_Lean_Parser_identEqFn___closed__2();
lean_mark_persistent(l_Lean_Parser_identEqFn___closed__2);
l_Lean_Parser_identEqFn___closed__3 = _init_l_Lean_Parser_identEqFn___closed__3();
lean_mark_persistent(l_Lean_Parser_identEqFn___closed__3);
l_Lean_Parser_hygieneInfoFn___lambda__1___closed__1 = _init_l_Lean_Parser_hygieneInfoFn___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_hygieneInfoFn___lambda__1___closed__1);
l_Lean_Parser_hygieneInfoFn___lambda__1___closed__2 = _init_l_Lean_Parser_hygieneInfoFn___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_hygieneInfoFn___lambda__1___closed__2);
l_Lean_Parser_hygieneInfoNoAntiquot___closed__1 = _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__1();
lean_mark_persistent(l_Lean_Parser_hygieneInfoNoAntiquot___closed__1);
l_Lean_Parser_hygieneInfoNoAntiquot___closed__2 = _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__2();
lean_mark_persistent(l_Lean_Parser_hygieneInfoNoAntiquot___closed__2);
l_Lean_Parser_hygieneInfoNoAntiquot___closed__3 = _init_l_Lean_Parser_hygieneInfoNoAntiquot___closed__3();
lean_mark_persistent(l_Lean_Parser_hygieneInfoNoAntiquot___closed__3);
l_Lean_Parser_hygieneInfoNoAntiquot = _init_l_Lean_Parser_hygieneInfoNoAntiquot();
lean_mark_persistent(l_Lean_Parser_hygieneInfoNoAntiquot);
l_Lean_Parser_invalidLongestMatchParser___closed__1 = _init_l_Lean_Parser_invalidLongestMatchParser___closed__1();
lean_mark_persistent(l_Lean_Parser_invalidLongestMatchParser___closed__1);
l_Lean_Parser_longestMatchStep___closed__1 = _init_l_Lean_Parser_longestMatchStep___closed__1();
lean_mark_persistent(l_Lean_Parser_longestMatchStep___closed__1);
l_Lean_Parser_longestMatchStep___closed__2 = _init_l_Lean_Parser_longestMatchStep___closed__2();
lean_mark_persistent(l_Lean_Parser_longestMatchStep___closed__2);
l_Lean_Parser_longestMatchFn___closed__1 = _init_l_Lean_Parser_longestMatchFn___closed__1();
lean_mark_persistent(l_Lean_Parser_longestMatchFn___closed__1);
l_Lean_Parser_anyOfFn___closed__1 = _init_l_Lean_Parser_anyOfFn___closed__1();
lean_mark_persistent(l_Lean_Parser_anyOfFn___closed__1);
l___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1);
l___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2);
l___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_checkColEq_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1);
l___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2);
l___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_checkColGe_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1);
l___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2);
l___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_checkColGt_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1);
l___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2);
l___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_checkLineEq_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1);
l___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2);
l___regBuiltin_Lean_Parser_withPosition_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_withPosition_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_withPosition_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_withPosition_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1);
l___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2);
l___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_withoutPosition_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_withoutPosition___closed__1 = _init_l_Lean_Parser_withoutPosition___closed__1();
lean_mark_persistent(l_Lean_Parser_withoutPosition___closed__1);
l___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1);
l___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2);
l___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_withForbidden_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1);
l___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2);
l___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_withoutForbidden_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_withoutForbidden___closed__1 = _init_l_Lean_Parser_withoutForbidden___closed__1();
lean_mark_persistent(l_Lean_Parser_withoutForbidden___closed__1);
l_Lean_Parser_eoiFn___closed__1 = _init_l_Lean_Parser_eoiFn___closed__1();
lean_mark_persistent(l_Lean_Parser_eoiFn___closed__1);
l_Lean_Parser_eoi___closed__1 = _init_l_Lean_Parser_eoi___closed__1();
lean_mark_persistent(l_Lean_Parser_eoi___closed__1);
l_Lean_Parser_eoi___closed__2 = _init_l_Lean_Parser_eoi___closed__2();
lean_mark_persistent(l_Lean_Parser_eoi___closed__2);
l_Lean_Parser_eoi = _init_l_Lean_Parser_eoi();
lean_mark_persistent(l_Lean_Parser_eoi);
l_Lean_Parser_TokenMap_instForInProdNameList___closed__1 = _init_l_Lean_Parser_TokenMap_instForInProdNameList___closed__1();
lean_mark_persistent(l_Lean_Parser_TokenMap_instForInProdNameList___closed__1);
l_Lean_Parser_TokenMap_instForInProdNameList___closed__2 = _init_l_Lean_Parser_TokenMap_instForInProdNameList___closed__2();
lean_mark_persistent(l_Lean_Parser_TokenMap_instForInProdNameList___closed__2);
l_Lean_Parser_instInhabitedPrattParsingTables___closed__1 = _init_l_Lean_Parser_instInhabitedPrattParsingTables___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedPrattParsingTables___closed__1);
l_Lean_Parser_instInhabitedPrattParsingTables = _init_l_Lean_Parser_instInhabitedPrattParsingTables();
lean_mark_persistent(l_Lean_Parser_instInhabitedPrattParsingTables);
l_Lean_Parser_instInhabitedLeadingIdentBehavior = _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior();
l_Lean_Parser_instBEqLeadingIdentBehavior___closed__1 = _init_l_Lean_Parser_instBEqLeadingIdentBehavior___closed__1();
lean_mark_persistent(l_Lean_Parser_instBEqLeadingIdentBehavior___closed__1);
l_Lean_Parser_instBEqLeadingIdentBehavior = _init_l_Lean_Parser_instBEqLeadingIdentBehavior();
lean_mark_persistent(l_Lean_Parser_instBEqLeadingIdentBehavior);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__1 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__1();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__1);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__2 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__2();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__2);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__3 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__3();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__3);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__4 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__4();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__4);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__5 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__5();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__5);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__6 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__6();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__6);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__7 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__7();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__7);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__8 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__8();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__8);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__9 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__9();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__9);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__10 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__10();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__10);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__11 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__11();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__11);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__12 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__12();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__12);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__13 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__13();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__13);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__14 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__14();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__14);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__15 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__15();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__15);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__16 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__16();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__16);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__17 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__17();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__17);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__18 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__18();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__18);
l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__19 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__19();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_reprLeadingIdentBehavior____x40_Lean_Parser_Basic___hyg_8982____closed__19);
l_Lean_Parser_instReprLeadingIdentBehavior___closed__1 = _init_l_Lean_Parser_instReprLeadingIdentBehavior___closed__1();
lean_mark_persistent(l_Lean_Parser_instReprLeadingIdentBehavior___closed__1);
l_Lean_Parser_instReprLeadingIdentBehavior = _init_l_Lean_Parser_instReprLeadingIdentBehavior();
lean_mark_persistent(l_Lean_Parser_instReprLeadingIdentBehavior);
l_Lean_Parser_instInhabitedParserCategory___closed__1 = _init_l_Lean_Parser_instInhabitedParserCategory___closed__1();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserCategory___closed__1);
l_Lean_Parser_instInhabitedParserCategory___closed__2 = _init_l_Lean_Parser_instInhabitedParserCategory___closed__2();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserCategory___closed__2);
l_Lean_Parser_instInhabitedParserCategory___closed__3 = _init_l_Lean_Parser_instInhabitedParserCategory___closed__3();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserCategory___closed__3);
l_Lean_Parser_instInhabitedParserCategory = _init_l_Lean_Parser_instInhabitedParserCategory();
lean_mark_persistent(l_Lean_Parser_instInhabitedParserCategory);
l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9445____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9445____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9445____closed__1);
if (builtin) {res = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9445_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_categoryParserFnRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_categoryParserFnRef);
lean_dec_ref(res);
}l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9471____lambda__1___closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9471____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9471____lambda__1___closed__1);
l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9471____closed__1 = _init_l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9471____closed__1();
lean_mark_persistent(l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9471____closed__1);
if (builtin) {res = l_Lean_Parser_initFn____x40_Lean_Parser_Basic___hyg_9471_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_categoryParserFnExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_categoryParserFnExtension);
lean_dec_ref(res);
}l_Lean_Parser_categoryParserFn___lambda__1___closed__1 = _init_l_Lean_Parser_categoryParserFn___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_categoryParserFn___lambda__1___closed__1);
l_Lean_Parser_categoryParserFn___closed__1 = _init_l_Lean_Parser_categoryParserFn___closed__1();
lean_mark_persistent(l_Lean_Parser_categoryParserFn___closed__1);
l_Lean_Parser_categoryParserFn___closed__2 = _init_l_Lean_Parser_categoryParserFn___closed__2();
lean_mark_persistent(l_Lean_Parser_categoryParserFn___closed__2);
l_Lean_Parser_categoryParserFn___closed__3 = _init_l_Lean_Parser_categoryParserFn___closed__3();
lean_mark_persistent(l_Lean_Parser_categoryParserFn___closed__3);
l_Lean_Parser_termParser___closed__1 = _init_l_Lean_Parser_termParser___closed__1();
lean_mark_persistent(l_Lean_Parser_termParser___closed__1);
l_Lean_Parser_termParser___closed__2 = _init_l_Lean_Parser_termParser___closed__2();
lean_mark_persistent(l_Lean_Parser_termParser___closed__2);
l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1);
l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2);
l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_checkNoImmediateColon___elambda__1___closed__1 = _init_l_Lean_Parser_checkNoImmediateColon___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_checkNoImmediateColon___elambda__1___closed__1);
l_Lean_Parser_checkNoImmediateColon___closed__1 = _init_l_Lean_Parser_checkNoImmediateColon___closed__1();
lean_mark_persistent(l_Lean_Parser_checkNoImmediateColon___closed__1);
l_Lean_Parser_checkNoImmediateColon___closed__2 = _init_l_Lean_Parser_checkNoImmediateColon___closed__2();
lean_mark_persistent(l_Lean_Parser_checkNoImmediateColon___closed__2);
l_Lean_Parser_checkNoImmediateColon = _init_l_Lean_Parser_checkNoImmediateColon();
lean_mark_persistent(l_Lean_Parser_checkNoImmediateColon);
l_Lean_Parser_pushNone___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_pushNone___elambda__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Parser_pushNone___elambda__1___rarg___closed__1);
l_Lean_Parser_pushNone___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_pushNone___elambda__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Parser_pushNone___elambda__1___rarg___closed__2);
l_Lean_Parser_pushNone___closed__1 = _init_l_Lean_Parser_pushNone___closed__1();
lean_mark_persistent(l_Lean_Parser_pushNone___closed__1);
l_Lean_Parser_pushNone___closed__2 = _init_l_Lean_Parser_pushNone___closed__2();
lean_mark_persistent(l_Lean_Parser_pushNone___closed__2);
l_Lean_Parser_pushNone = _init_l_Lean_Parser_pushNone();
lean_mark_persistent(l_Lean_Parser_pushNone);
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
l_Lean_Parser_antiquotNestedExpr___closed__9 = _init_l_Lean_Parser_antiquotNestedExpr___closed__9();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___closed__9);
l_Lean_Parser_antiquotNestedExpr___closed__10 = _init_l_Lean_Parser_antiquotNestedExpr___closed__10();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr___closed__10);
l_Lean_Parser_antiquotNestedExpr = _init_l_Lean_Parser_antiquotNestedExpr();
lean_mark_persistent(l_Lean_Parser_antiquotNestedExpr);
l_Lean_Parser_antiquotExpr___closed__1 = _init_l_Lean_Parser_antiquotExpr___closed__1();
lean_mark_persistent(l_Lean_Parser_antiquotExpr___closed__1);
l_Lean_Parser_antiquotExpr___closed__2 = _init_l_Lean_Parser_antiquotExpr___closed__2();
lean_mark_persistent(l_Lean_Parser_antiquotExpr___closed__2);
l_Lean_Parser_antiquotExpr___closed__3 = _init_l_Lean_Parser_antiquotExpr___closed__3();
lean_mark_persistent(l_Lean_Parser_antiquotExpr___closed__3);
l_Lean_Parser_antiquotExpr___closed__4 = _init_l_Lean_Parser_antiquotExpr___closed__4();
lean_mark_persistent(l_Lean_Parser_antiquotExpr___closed__4);
l_Lean_Parser_antiquotExpr = _init_l_Lean_Parser_antiquotExpr();
lean_mark_persistent(l_Lean_Parser_antiquotExpr);
l_Lean_Parser_tokenAntiquotFn___lambda__1___closed__1 = _init_l_Lean_Parser_tokenAntiquotFn___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_tokenAntiquotFn___lambda__1___closed__1);
l_Lean_Parser_tokenAntiquotFn___lambda__1___closed__2 = _init_l_Lean_Parser_tokenAntiquotFn___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Parser_tokenAntiquotFn___lambda__1___closed__2);
l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__1 = _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__1);
l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__2 = _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__2);
l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__3 = _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__3);
l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__4 = _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__4);
l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__5 = _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__5);
l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__6 = _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__6);
l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__7 = _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__7);
l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__8 = _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__8);
l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__9 = _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__9);
l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__10 = _init_l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__10();
lean_mark_persistent(l_Lean_Parser_tokenAntiquotFn___lambda__2___closed__10);
l_Lean_Parser_instCoeStringParser___closed__1 = _init_l_Lean_Parser_instCoeStringParser___closed__1();
lean_mark_persistent(l_Lean_Parser_instCoeStringParser___closed__1);
l_Lean_Parser_instCoeStringParser = _init_l_Lean_Parser_instCoeStringParser();
lean_mark_persistent(l_Lean_Parser_instCoeStringParser);
l___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1);
l___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2);
l___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_mkAntiquot_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_mkAntiquot___closed__1 = _init_l_Lean_Parser_mkAntiquot___closed__1();
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
l___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1);
l___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2);
l___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_withAntiquot_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1);
l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2);
l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_mkAntiquotSplice___closed__1 = _init_l_Lean_Parser_mkAntiquotSplice___closed__1();
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
l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__1 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__1);
l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__2 = _init_l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___lambda__1___closed__2);
l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1 = _init_l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1);
l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2 = _init_l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2);
l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__3 = _init_l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_sepByElemParser___closed__1 = _init_l_Lean_Parser_sepByElemParser___closed__1();
lean_mark_persistent(l_Lean_Parser_sepByElemParser___closed__1);
l_Lean_Parser_sepByElemParser___closed__2 = _init_l_Lean_Parser_sepByElemParser___closed__2();
lean_mark_persistent(l_Lean_Parser_sepByElemParser___closed__2);
l_Lean_Parser_sepByElemParser___closed__3 = _init_l_Lean_Parser_sepByElemParser___closed__3();
lean_mark_persistent(l_Lean_Parser_sepByElemParser___closed__3);
l_Lean_Parser_fieldIdxFn___closed__1 = _init_l_Lean_Parser_fieldIdxFn___closed__1();
lean_mark_persistent(l_Lean_Parser_fieldIdxFn___closed__1);
l_Lean_Parser_fieldIdxFn___closed__2 = _init_l_Lean_Parser_fieldIdxFn___closed__2();
lean_mark_persistent(l_Lean_Parser_fieldIdxFn___closed__2);
l_Lean_Parser_fieldIdxFn___closed__3 = _init_l_Lean_Parser_fieldIdxFn___closed__3();
lean_mark_persistent(l_Lean_Parser_fieldIdxFn___closed__3);
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
l_Lean_Parser_fieldIdx = _init_l_Lean_Parser_fieldIdx();
lean_mark_persistent(l_Lean_Parser_fieldIdx);
l_Lean_Parser_skip___closed__1 = _init_l_Lean_Parser_skip___closed__1();
lean_mark_persistent(l_Lean_Parser_skip___closed__1);
l_Lean_Parser_skip___closed__2 = _init_l_Lean_Parser_skip___closed__2();
lean_mark_persistent(l_Lean_Parser_skip___closed__2);
l_Lean_Parser_skip = _init_l_Lean_Parser_skip();
lean_mark_persistent(l_Lean_Parser_skip);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
