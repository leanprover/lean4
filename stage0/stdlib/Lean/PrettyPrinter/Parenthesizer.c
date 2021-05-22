// Lean compiler output
// Module: Lean.PrettyPrinter.Parenthesizer
// Imports: Init Lean.CoreM Lean.KeyedDeclsAttribute Lean.Parser.Extension Lean.ParserCompiler.Attribute Lean.PrettyPrinter.Basic
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
extern lean_object* l_instReprOption___rarg___closed__2;
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withoutInfo_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer(lean_object*);
uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__13;
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__1;
extern lean_object* l_Lean_Parser_Tactic_first___closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___rarg(lean_object*);
uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PrettyPrinter_categoryParenthesizerAttribute;
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_optionalNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesize___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__3;
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_parenthesize___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__21;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__4;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__4___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_evalInsideQuot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_up(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__7;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__10;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__10;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
extern lean_object* l_Lean_instInhabitedKeyedDeclsAttribute___closed__4;
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_parenthesize___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_StateRefT_x27_instMonadLiftStateRefT_x27___closed__1;
extern lean_object* l_term___u2218_____closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__7;
extern lean_object* l_Std_Format_join___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Context_cat___default;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___boxed(lean_object*);
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__7;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3346_(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__17;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeArrowParenthesizerParenthesizerParenthesizerAliasValue(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_evalInsideQuot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withoutPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__15;
lean_object* l_Lean_PrettyPrinter_ParenthesizerM_orelse(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_State_trailCat___default;
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__27;
lean_object* l_List_range(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_parenthesizeCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_State_trailPrec___default;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedByCategoryToken_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_paren___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_instOrElseParenthesizerM(lean_object*);
lean_object* l_IO_mkRef___at_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3009____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instReprProd___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
lean_object* l_Lean_PrettyPrinter_runForNodeKind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__9;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back_x3f___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__11;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_atomic_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_dbgTraceState_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_registerAlias(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__22;
lean_object* l_List_forM___at_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_parenthesize___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2(lean_object*);
extern lean_object* l_Lean_Syntax_getKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerAliasCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__3;
lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_pretty_printer_parenthesizer_interpret_parser_descr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__3;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesize___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__7;
lean_object* l_ReaderT_instMonadLiftReaderT(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
extern lean_object* l_term___x24_______closed__8;
lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_many1NoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__24;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__5;
lean_object* l_Lean_Syntax_Traverser_setCur(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__18;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__15;
extern lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__25;
extern lean_object* l_term___x24_______closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_dbgTraceState_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadRefCoreM;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind___closed__2;
extern lean_object* l_termS_x21_____closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_suppressInsideQuot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ParenthesizerM_orelse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withForbidden_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Unhygienic_run___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedByCategoryToken_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__12;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_incQuotDepth_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__28;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParserOfStack_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__14;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__3(lean_object*);
lean_object* l_ReaderT_instMonadFunctorReaderT___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_intro___closed__10;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_parenthesize___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withoutForbidden_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__23;
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_parenthesize___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_PP_Result_quote___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM(lean_object*);
extern lean_object* l_Lean_Parser_maxPrec;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMCtxMetaM___closed__1;
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__11;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepBy1NoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getValues___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__11;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__10;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__11;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__20;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__9;
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs___closed__1;
extern lean_object* l_Std_Format_paren___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_State_contPrec___default;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__13;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_many1Unbox_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__4;
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___boxed(lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__8;
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__12;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__10;
extern lean_object* l_Lean_Parser_Tactic_paren___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PrettyPrinter_Parenthesizer_State_visitedToken___default;
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__16;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_71____closed__2;
extern lean_object* l_Lean_KernelException_toMessageData___closed__3;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__1;
extern lean_object* l_Lean_Level_PP_Result_quote___closed__1;
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__9;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_evalInsideQuot_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__2;
lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__4(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__9;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__4;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1318____closed__8;
extern lean_object* l_term_x5b___x5d___closed__5;
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_decQuotDepth_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_down(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeArrowParenthesizerArrowParenthesizerParenthesizerParenthesizerAliasValue(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3009_(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076_(lean_object*);
extern lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1318____closed__9;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer(lean_object*);
uint8_t l_Lean_Parser_isParserCategory(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedByCategoryToken_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__10;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_dbgTraceState_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__3;
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_right(lean_object*);
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_mkParenthesizerAttribute___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withForbidden_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1;
lean_object* l_Lean_PrettyPrinter_parenthesize_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeCommand___closed__1;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___boxed(lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_fmt___at_Lean_Level_PP_Result_format___spec__2(lean_object*);
lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__3___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_tactic___x3c_x3b_x3e_____closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__19;
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*);
lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1879____closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__3;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12862____closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesize_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__16;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_first___closed__6;
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeParenthesizerParenthesizerAliasValue(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_mkParenthesizerAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__26;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM_match__1(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___rarg(lean_object*);
extern lean_object* l_prec_x28___x29___closed__7;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Substring_splitOn_loop___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_State_contCat___default;
lean_object* l_Lean_PrettyPrinter_instOrElseParenthesizerM___closed__1;
extern lean_object* l_Array_term_____x5b___x3a___x5d___closed__6;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_parenthesize___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_prec_x28___x29___closed__3;
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__6;
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___boxed(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_4320____closed__4;
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withForbidden_parenthesizer___boxed(lean_object*);
extern lean_object* l_unexpand____x40_Init_Notation___hyg_1981____closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_State_minPrec___default;
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_15488____closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___boxed__const__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___closed__1;
lean_object* l_Nat_min(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_backtrackExceptionId;
lean_object* l_Lean_PrettyPrinter_parenthesizeTerm___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__3;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__11;
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
extern lean_object* l_instReprOption___rarg___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1;
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParserOfStack_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1198____closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__5(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesize___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_interpolatedStrLitKind;
extern lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__12;
lean_object* l_Lean_PrettyPrinter_parenthesize___closed__4;
extern lean_object* l_Std_Format_paren___closed__3;
lean_object* l_Lean_instMonadRef___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_antiquot_parenthesizer(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getId(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_Context_cat___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_State_contPrec___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_State_contCat___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_State_minPrec___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_State_trailPrec___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_State_trailCat___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static uint8_t _init_l_Lean_PrettyPrinter_Parenthesizer_State_visitedToken___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_ParenthesizerM_orelse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_13, 1);
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
x_23 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_24 = lean_nat_dec_eq(x_23, x_22);
lean_dec(x_22);
if (x_24 == 0)
{
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_13);
lean_dec(x_14);
x_25 = lean_st_ref_get(x_6, x_20);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_set(x_4, x_11, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_dec(x_13);
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
x_32 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_33 = lean_nat_dec_eq(x_32, x_31);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_14);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_14);
x_35 = lean_st_ref_get(x_6, x_30);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_set(x_4, x_11, x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_38);
return x_39;
}
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_ParenthesizerM_orelse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ParenthesizerM_orelse___rarg), 7, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_instOrElseParenthesizerM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ParenthesizerM_orelse___rarg), 7, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_instOrElseParenthesizerM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_instOrElseParenthesizerM___closed__1;
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_mkParenthesizerAttribute___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 3);
x_6 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_2, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [parenthesizer] argument, unknown syntax kind '");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_3);
x_11 = l_Lean_Attribute_Builtin_getId(x_2, x_3, x_4, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
if (x_1 == 0)
{
lean_object* x_25; 
lean_free_object(x_6);
x_25 = lean_box(0);
x_15 = x_25;
goto block_24;
}
else
{
lean_object* x_26; 
lean_inc(x_12);
lean_inc(x_10);
x_26 = lean_environment_find(x_10, x_12);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_free_object(x_6);
x_27 = lean_box(0);
x_15 = x_27;
goto block_24;
}
else
{
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_ctor_set(x_6, 1, x_13);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
}
block_24:
{
uint8_t x_16; 
lean_dec(x_15);
x_16 = l_Lean_Parser_isValidSyntaxNodeKind(x_10, x_12);
lean_dec(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
x_17 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_18 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_KernelException_toMessageData___closed__3;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at_Lean_PrettyPrinter_mkParenthesizerAttribute___spec__1(x_21, x_3, x_4, x_13);
lean_dec(x_3);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_3);
if (lean_is_scalar(x_14)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_14;
}
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_free_object(x_6);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
return x_11;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_6, 0);
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_6);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_3);
x_35 = l_Lean_Attribute_Builtin_getId(x_2, x_3, x_4, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
if (x_1 == 0)
{
lean_object* x_49; 
x_49 = lean_box(0);
x_39 = x_49;
goto block_48;
}
else
{
lean_object* x_50; 
lean_inc(x_36);
lean_inc(x_34);
x_50 = lean_environment_find(x_34, x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_box(0);
x_39 = x_51;
goto block_48;
}
else
{
lean_object* x_52; 
lean_dec(x_50);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_3);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_36);
lean_ctor_set(x_52, 1, x_37);
return x_52;
}
}
block_48:
{
uint8_t x_40; 
lean_dec(x_39);
x_40 = l_Lean_Parser_isValidSyntaxNodeKind(x_34, x_36);
lean_dec(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_38);
x_41 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_41, 0, x_36);
x_42 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_KernelException_toMessageData___closed__3;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_throwError___at_Lean_PrettyPrinter_mkParenthesizerAttribute___spec__1(x_45, x_3, x_4, x_37);
lean_dec(x_3);
return x_46;
}
else
{
lean_object* x_47; 
lean_dec(x_3);
if (lean_is_scalar(x_38)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_38;
}
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_37);
return x_47;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_34);
lean_dec(x_3);
x_53 = lean_ctor_get(x_35, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_35, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_55 = x_35;
} else {
 lean_dec_ref(x_35);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinParenthesizer");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesizer");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PrettyPrinter");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__2;
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parenthesizer");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Register a parenthesizer for a parser.\n\n  [parenthesizer k] registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` for the `SyntaxNodeKind` `k`.");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__2;
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
x_3 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
x_4 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
x_5 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__10;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesizerAttribute");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__11;
x_3 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__13;
x_4 = l_Lean_KeyedDeclsAttribute_init___rarg(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_mkParenthesizerAttribute___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_PrettyPrinter_mkParenthesizerAttribute___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [parenthesizer] argument, unknown parser category '");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_3);
x_10 = l_Lean_Attribute_Builtin_getId(x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_Parser_isParserCategory(x_9, x_12);
lean_dec(x_9);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_10);
x_15 = 1;
x_16 = l_Lean_Name_toString(x_12, x_15);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
x_18 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_KernelException_toMessageData___closed__3;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at_Lean_PrettyPrinter_mkParenthesizerAttribute___spec__1(x_21, x_3, x_4, x_13);
lean_dec(x_3);
return x_22;
}
else
{
lean_dec(x_3);
return x_10;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = l_Lean_Parser_isParserCategory(x_9, x_23);
lean_dec(x_9);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = 1;
x_27 = l_Lean_Name_toString(x_23, x_26);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
x_29 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_KernelException_toMessageData___closed__3;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_PrettyPrinter_mkParenthesizerAttribute___spec__1(x_32, x_3, x_4, x_24);
lean_dec(x_3);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_3);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_24);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_9);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
return x_10;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_10, 0);
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_10);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinCategoryParenthesizer");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("categoryParenthesizer");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CategoryParenthesizer");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_2 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Register a parenthesizer for a syntax category.\n\n  [parenthesizer cat] registers a declaration of type `Lean.PrettyPrinter.CategoryParenthesizer` for the category `cat`,\n  which is used when parenthesizing calls of `categoryParser cat prec`. Implementations should call `maybeParenthesize`\n  with the precedence and `cat`. If no category parenthesizer is registered, the category will never be parenthesized,\n  but still be traversed for parenthesizing nested categories.");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__2;
x_2 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__4;
x_3 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__7;
x_4 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__6;
x_5 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__8;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("categoryParenthesizerAttribute");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_2 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__9;
x_3 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__11;
x_4 = l_Lean_KeyedDeclsAttribute_init___rarg(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("combinatorParenthesizer");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Register a parenthesizer for a parser combinator.\n\n  [combinatorParenthesizer c] registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` for the `Parser` declaration `c`.\n  Note that, unlike with [parenthesizer], this is not a node kind since combinators usually do not introduce their own node kinds.\n  The tagged declaration may optionally accept parameters corresponding to (a prefix of) those of `c`, where `Parser` is replaced\n  with `Parenthesizer` in the parameter types.");
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
x_3 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__3;
x_4 = l_Lean_ParserCompiler_registerCombinatorAttribute(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM_match__1___rarg), 2, 0);
return x_3;
}
}
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_apply_1(x_1, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_apply_1(x_1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___spec__1___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_1);
x_14 = lean_st_ref_set(x_3, x_10, x_11);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_10, 1);
x_22 = lean_ctor_get(x_10, 2);
x_23 = lean_ctor_get(x_10, 3);
x_24 = lean_ctor_get(x_10, 4);
x_25 = lean_ctor_get(x_10, 5);
x_26 = lean_ctor_get_uint8(x_10, sizeof(void*)*6);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_27 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set(x_27, 5, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*6, x_26);
x_28 = lean_st_ref_set(x_3, x_27, x_11);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_box(0);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_apply_1(x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_ctor_set(x_11, 0, x_17);
x_18 = lean_st_ref_set(x_4, x_11, x_12);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_16);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get(x_11, 3);
x_27 = lean_ctor_get(x_11, 4);
x_28 = lean_ctor_get(x_11, 5);
x_29 = lean_ctor_get_uint8(x_11, sizeof(void*)*6);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_30 = lean_apply_1(x_2, x_23);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_24);
lean_ctor_set(x_33, 2, x_25);
lean_ctor_set(x_33, 3, x_26);
lean_ctor_set(x_33, 4, x_27);
lean_ctor_set(x_33, 5, x_28);
lean_ctor_set_uint8(x_33, sizeof(void*)*6, x_29);
x_34 = lean_st_ref_set(x_4, x_33, x_12);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__1;
x_2 = l_Lean_Meta_instMonadMCtxMetaM___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___spec__1___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__3___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__2;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__3;
x_3 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__5;
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 3);
x_15 = lean_ctor_get(x_10, 1);
lean_dec(x_15);
x_16 = l_Nat_min(x_1, x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_inc(x_17);
lean_ctor_set(x_10, 3, x_17);
lean_ctor_set(x_10, 1, x_17);
x_18 = lean_st_ref_set(x_3, x_10, x_12);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = l_Nat_min(x_26, x_1);
lean_dec(x_26);
lean_ctor_set(x_14, 0, x_27);
lean_ctor_set(x_10, 1, x_17);
x_28 = lean_st_ref_set(x_3, x_10, x_12);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_14, 0);
lean_inc(x_35);
lean_dec(x_14);
x_36 = l_Nat_min(x_35, x_1);
lean_dec(x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_10, 3, x_37);
lean_ctor_set(x_10, 1, x_17);
x_38 = lean_st_ref_set(x_3, x_10, x_12);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_10, 0);
x_44 = lean_ctor_get(x_10, 2);
x_45 = lean_ctor_get(x_10, 3);
x_46 = lean_ctor_get(x_10, 4);
x_47 = lean_ctor_get(x_10, 5);
x_48 = lean_ctor_get_uint8(x_10, sizeof(void*)*6);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_10);
x_49 = l_Nat_min(x_1, x_1);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_inc(x_50);
x_51 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_44);
lean_ctor_set(x_51, 3, x_50);
lean_ctor_set(x_51, 4, x_46);
lean_ctor_set(x_51, 5, x_47);
lean_ctor_set_uint8(x_51, sizeof(void*)*6, x_48);
x_52 = lean_st_ref_set(x_3, x_51, x_12);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_57 = lean_ctor_get(x_45, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_58 = x_45;
} else {
 lean_dec_ref(x_45);
 x_58 = lean_box(0);
}
x_59 = l_Nat_min(x_57, x_1);
lean_dec(x_57);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_61, 0, x_43);
lean_ctor_set(x_61, 1, x_50);
lean_ctor_set(x_61, 2, x_44);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set(x_61, 4, x_46);
lean_ctor_set(x_61, 5, x_47);
lean_ctor_set_uint8(x_61, sizeof(void*)*6, x_48);
x_62 = lean_st_ref_set(x_3, x_61, x_12);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_9, 1);
lean_inc(x_67);
lean_dec(x_9);
x_68 = !lean_is_exclusive(x_10);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_10, 3);
x_70 = lean_ctor_get(x_10, 1);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_11);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_11, 0);
x_73 = l_Nat_min(x_72, x_1);
lean_dec(x_72);
lean_ctor_set(x_11, 0, x_73);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = l_Nat_min(x_1, x_1);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_10, 3, x_75);
x_76 = lean_st_ref_set(x_3, x_10, x_67);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
x_79 = lean_box(0);
lean_ctor_set(x_76, 0, x_79);
return x_76;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_dec(x_76);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_69);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_69, 0);
x_85 = l_Nat_min(x_84, x_1);
lean_dec(x_84);
lean_ctor_set(x_69, 0, x_85);
x_86 = lean_st_ref_set(x_3, x_10, x_67);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
x_89 = lean_box(0);
lean_ctor_set(x_86, 0, x_89);
return x_86;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec(x_86);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_93 = lean_ctor_get(x_69, 0);
lean_inc(x_93);
lean_dec(x_69);
x_94 = l_Nat_min(x_93, x_1);
lean_dec(x_93);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_10, 3, x_95);
x_96 = lean_st_ref_set(x_3, x_10, x_67);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
x_99 = lean_box(0);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_97);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_11, 0);
lean_inc(x_101);
lean_dec(x_11);
x_102 = l_Nat_min(x_101, x_1);
lean_dec(x_101);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = l_Nat_min(x_1, x_1);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_10, 3, x_105);
lean_ctor_set(x_10, 1, x_103);
x_106 = lean_st_ref_set(x_3, x_10, x_67);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_109 = lean_box(0);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_111 = lean_ctor_get(x_69, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_112 = x_69;
} else {
 lean_dec_ref(x_69);
 x_112 = lean_box(0);
}
x_113 = l_Nat_min(x_111, x_1);
lean_dec(x_111);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(1, 1, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_10, 3, x_114);
lean_ctor_set(x_10, 1, x_103);
x_115 = lean_st_ref_set(x_3, x_10, x_67);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
x_118 = lean_box(0);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_120 = lean_ctor_get(x_10, 0);
x_121 = lean_ctor_get(x_10, 2);
x_122 = lean_ctor_get(x_10, 3);
x_123 = lean_ctor_get(x_10, 4);
x_124 = lean_ctor_get(x_10, 5);
x_125 = lean_ctor_get_uint8(x_10, sizeof(void*)*6);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_10);
x_126 = lean_ctor_get(x_11, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_127 = x_11;
} else {
 lean_dec_ref(x_11);
 x_127 = lean_box(0);
}
x_128 = l_Nat_min(x_126, x_1);
lean_dec(x_126);
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(1, 1, 0);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_128);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_130 = l_Nat_min(x_1, x_1);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_132, 0, x_120);
lean_ctor_set(x_132, 1, x_129);
lean_ctor_set(x_132, 2, x_121);
lean_ctor_set(x_132, 3, x_131);
lean_ctor_set(x_132, 4, x_123);
lean_ctor_set(x_132, 5, x_124);
lean_ctor_set_uint8(x_132, sizeof(void*)*6, x_125);
x_133 = lean_st_ref_set(x_3, x_132, x_67);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_135 = x_133;
} else {
 lean_dec_ref(x_133);
 x_135 = lean_box(0);
}
x_136 = lean_box(0);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_135;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_138 = lean_ctor_get(x_122, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_139 = x_122;
} else {
 lean_dec_ref(x_122);
 x_139 = lean_box(0);
}
x_140 = l_Nat_min(x_138, x_1);
lean_dec(x_138);
if (lean_is_scalar(x_139)) {
 x_141 = lean_alloc_ctor(1, 1, 0);
} else {
 x_141 = x_139;
}
lean_ctor_set(x_141, 0, x_140);
x_142 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_142, 0, x_120);
lean_ctor_set(x_142, 1, x_129);
lean_ctor_set(x_142, 2, x_121);
lean_ctor_set(x_142, 3, x_141);
lean_ctor_set(x_142, 4, x_123);
lean_ctor_set(x_142, 5, x_124);
lean_ctor_set_uint8(x_142, sizeof(void*)*6, x_125);
x_143 = lean_st_ref_set(x_3, x_142, x_67);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_145 = x_143;
} else {
 lean_dec_ref(x_143);
 x_145 = lean_box(0);
}
x_146 = lean_box(0);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_144);
return x_147;
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_st_ref_get(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_st_ref_take(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = l_Lean_Syntax_Traverser_left(x_11);
lean_ctor_set(x_8, 0, x_12);
x_13 = lean_st_ref_set(x_1, x_8, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 2);
x_23 = lean_ctor_get(x_8, 3);
x_24 = lean_ctor_get(x_8, 4);
x_25 = lean_ctor_get(x_8, 5);
x_26 = lean_ctor_get_uint8(x_8, sizeof(void*)*6);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_27 = l_Lean_Syntax_Traverser_left(x_20);
x_28 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_23);
lean_ctor_set(x_28, 4, x_24);
lean_ctor_set(x_28, 5, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*6, x_26);
x_29 = lean_st_ref_set(x_1, x_28, x_9);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = l_Lean_Syntax_Traverser_down(x_13, x_1);
lean_ctor_set(x_10, 0, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
x_25 = lean_ctor_get(x_10, 3);
x_26 = lean_ctor_get(x_10, 4);
x_27 = lean_ctor_get(x_10, 5);
x_28 = lean_ctor_get_uint8(x_10, sizeof(void*)*6);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_29 = l_Lean_Syntax_Traverser_down(x_22, x_1);
x_30 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_25);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*6, x_28);
x_31 = lean_st_ref_set(x_3, x_30, x_11);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_st_ref_take(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = l_Lean_Syntax_Traverser_up(x_11);
lean_ctor_set(x_8, 0, x_12);
x_13 = lean_st_ref_set(x_1, x_8, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 2);
x_23 = lean_ctor_get(x_8, 3);
x_24 = lean_ctor_get(x_8, 4);
x_25 = lean_ctor_get(x_8, 5);
x_26 = lean_ctor_get_uint8(x_8, sizeof(void*)*6);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_27 = l_Lean_Syntax_Traverser_up(x_20);
x_28 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_23);
lean_ctor_set(x_28, 4, x_24);
lean_ctor_set(x_28, 5, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*6, x_26);
x_29 = lean_st_ref_set(x_1, x_28, x_9);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_visitArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_visitArgs___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs___closed__1;
x_11 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_apply_6(x_10, x_15, x_2, x_3, x_4, x_5, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_12, x_17);
lean_dec(x_12);
x_19 = l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3(x_18, x_2, x_3, x_4, x_5, x_9);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg(x_3, x_4, x_5, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_apply_6(x_10, x_22, x_2, x_3, x_4, x_5, x_25);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLiftReaderT), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__2;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__3;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadFunctorReaderT___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__2;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadFunctorReaderT___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_StateRefT_x27_instMonadLiftStateRefT_x27___closed__1;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__5;
x_3 = l_Lean_Core_instMonadRefCoreM;
x_4 = l_Lean_instMonadRef___rarg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__1;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__4;
x_3 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__6;
x_4 = l_Lean_instMonadRef___rarg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1___rarg___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1___rarg___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___lambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__7;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__8;
x_3 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__9;
x_4 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__10;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__11;
return x_1;
}
}
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_apply_2(x_4, x_1, x_2);
return x_5;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_apply_2(x_4, x_1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 5);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
lean_dec(x_1);
x_10 = lean_box(x_9);
x_11 = lean_apply_7(x_2, x_7, x_3, x_4, x_5, x_6, x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 5);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
lean_dec(x_1);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_box(x_11);
x_14 = lean_apply_7(x_2, x_12, x_9, x_10, x_6, x_7, x_8, x_13);
return x_14;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__5___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_st_ref_get(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Array_back_x3f___rarg(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Array_back_x3f___rarg(x_18);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
return x_23;
}
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_Lean_checkTraceOption(x_7, x_1);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
lean_object* l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = 0;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_formatStxAux(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 3);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_1);
x_20 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_20, 0, x_1);
x_21 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__1;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__3;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_10);
x_26 = l_Lean_KernelException_toMessageData___closed__15;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Std_PersistentArray_push___rarg(x_19, x_29);
lean_ctor_set(x_14, 0, x_30);
x_31 = lean_st_ref_set(x_6, x_13, x_15);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_38 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_39 = lean_ctor_get(x_14, 0);
lean_inc(x_39);
lean_dec(x_14);
lean_inc(x_1);
x_40 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_40, 0, x_1);
x_41 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__1;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__3;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_10);
x_46 = l_Lean_KernelException_toMessageData___closed__15;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_47);
lean_inc(x_8);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_8);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Std_PersistentArray_push___rarg(x_39, x_49);
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_38);
lean_ctor_set(x_13, 3, x_51);
x_52 = lean_st_ref_set(x_6, x_13, x_15);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_57 = lean_ctor_get(x_13, 0);
x_58 = lean_ctor_get(x_13, 1);
x_59 = lean_ctor_get(x_13, 2);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_13);
x_60 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_61 = lean_ctor_get(x_14, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_62 = x_14;
} else {
 lean_dec_ref(x_14);
 x_62 = lean_box(0);
}
lean_inc(x_1);
x_63 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_63, 0, x_1);
x_64 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__1;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__3;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_10);
x_69 = l_Lean_KernelException_toMessageData___closed__15;
x_70 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_70);
lean_inc(x_8);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_8);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Std_PersistentArray_push___rarg(x_61, x_72);
if (lean_is_scalar(x_62)) {
 x_74 = lean_alloc_ctor(0, 1, 1);
} else {
 x_74 = x_62;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_60);
x_75 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_75, 0, x_57);
lean_ctor_set(x_75, 1, x_58);
lean_ctor_set(x_75, 2, x_59);
lean_ctor_set(x_75, 3, x_74);
x_76 = lean_st_ref_set(x_6, x_75, x_15);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
x_79 = lean_box(0);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = l_Lean_Syntax_Traverser_setCur(x_13, x_1);
lean_ctor_set(x_10, 0, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
x_25 = lean_ctor_get(x_10, 3);
x_26 = lean_ctor_get(x_10, 4);
x_27 = lean_ctor_get(x_10, 5);
x_28 = lean_ctor_get_uint8(x_10, sizeof(void*)*6);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_29 = l_Lean_Syntax_Traverser_setCur(x_22, x_1);
x_30 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_25);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*6, x_28);
x_31 = lean_st_ref_set(x_3, x_30, x_11);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_st_ref_take(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = l_Lean_Syntax_Traverser_right(x_11);
lean_ctor_set(x_8, 0, x_12);
x_13 = lean_st_ref_set(x_1, x_8, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 2);
x_23 = lean_ctor_get(x_8, 3);
x_24 = lean_ctor_get(x_8, 4);
x_25 = lean_ctor_get(x_8, 5);
x_26 = lean_ctor_get_uint8(x_8, sizeof(void*)*6);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_27 = l_Lean_Syntax_Traverser_right(x_20);
x_28 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_23);
lean_ctor_set(x_28, 4, x_24);
lean_ctor_set(x_28, 5, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*6, x_26);
x_29 = lean_st_ref_set(x_1, x_28, x_9);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___rarg___boxed), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instReprOption___rarg___closed__2;
x_2 = l_instReprProd___rarg___closed__1;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7___closed__1;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = 1;
x_5 = l_Lean_Name_toString(x_3, x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_7 = l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7___closed__2;
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Std_Format_paren___closed__3;
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Std_Format_paren___closed__4;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Std_Format_paren___closed__2;
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = 0;
x_16 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l_Std_fmt___at_Lean_Level_PP_Result_format___spec__2(x_17);
x_19 = l_instReprOption___rarg___closed__4;
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_instReprProd___rarg___closed__1;
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_box(1);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_6);
x_26 = l_Std_Format_paren___closed__3;
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Std_Format_paren___closed__4;
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Std_Format_paren___closed__2;
x_31 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = 0;
x_33 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
return x_33;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_11, 3);
lean_dec(x_14);
lean_ctor_set(x_11, 3, x_1);
x_15 = lean_st_ref_set(x_4, x_11, x_12);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
x_24 = lean_ctor_get(x_11, 2);
x_25 = lean_ctor_get(x_11, 4);
x_26 = lean_ctor_get(x_11, 5);
x_27 = lean_ctor_get_uint8(x_11, sizeof(void*)*6);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_28 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_1);
lean_ctor_set(x_28, 4, x_25);
lean_ctor_set(x_28, 5, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*6, x_27);
x_29 = lean_st_ref_set(x_4, x_28, x_12);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_st_ref_get(x_11, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_9, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (x_2 == 0)
{
lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_5);
x_17 = lean_ctor_get(x_16, 4);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_3);
x_20 = lean_st_ref_get(x_11, x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_take(x_9, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_23, 5);
lean_dec(x_26);
x_27 = lean_ctor_get(x_23, 4);
lean_dec(x_27);
lean_ctor_set(x_23, 5, x_4);
lean_ctor_set(x_23, 4, x_19);
x_28 = lean_st_ref_set(x_9, x_23, x_24);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(x_1, x_30, x_8, x_9, x_10, x_11, x_29);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
x_34 = lean_ctor_get(x_23, 2);
x_35 = lean_ctor_get(x_23, 3);
x_36 = lean_ctor_get_uint8(x_23, sizeof(void*)*6);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_37 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set(x_37, 3, x_35);
lean_ctor_set(x_37, 4, x_19);
lean_ctor_set(x_37, 5, x_4);
lean_ctor_set_uint8(x_37, sizeof(void*)*6, x_36);
x_38 = lean_st_ref_set(x_9, x_37, x_24);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(x_1, x_40, x_8, x_9, x_10, x_11, x_39);
return x_41;
}
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_15, 1);
lean_inc(x_42);
lean_dec(x_15);
x_43 = !lean_is_exclusive(x_17);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_44 = lean_ctor_get(x_17, 0);
x_45 = l_Nat_min(x_44, x_3);
lean_dec(x_3);
lean_dec(x_44);
lean_ctor_set(x_17, 0, x_45);
x_46 = lean_st_ref_get(x_11, x_42);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_st_ref_take(x_9, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_49, 5);
lean_dec(x_52);
x_53 = lean_ctor_get(x_49, 4);
lean_dec(x_53);
lean_ctor_set(x_49, 5, x_4);
lean_ctor_set(x_49, 4, x_17);
x_54 = lean_st_ref_set(x_9, x_49, x_50);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_box(0);
x_57 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(x_1, x_56, x_8, x_9, x_10, x_11, x_55);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_58 = lean_ctor_get(x_49, 0);
x_59 = lean_ctor_get(x_49, 1);
x_60 = lean_ctor_get(x_49, 2);
x_61 = lean_ctor_get(x_49, 3);
x_62 = lean_ctor_get_uint8(x_49, sizeof(void*)*6);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_49);
x_63 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_59);
lean_ctor_set(x_63, 2, x_60);
lean_ctor_set(x_63, 3, x_61);
lean_ctor_set(x_63, 4, x_17);
lean_ctor_set(x_63, 5, x_4);
lean_ctor_set_uint8(x_63, sizeof(void*)*6, x_62);
x_64 = lean_st_ref_set(x_9, x_63, x_50);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_box(0);
x_67 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(x_1, x_66, x_8, x_9, x_10, x_11, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_68 = lean_ctor_get(x_17, 0);
lean_inc(x_68);
lean_dec(x_17);
x_69 = l_Nat_min(x_68, x_3);
lean_dec(x_3);
lean_dec(x_68);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_st_ref_get(x_11, x_42);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_st_ref_take(x_9, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_74, 3);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_74, sizeof(void*)*6);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 lean_ctor_release(x_74, 4);
 lean_ctor_release(x_74, 5);
 x_81 = x_74;
} else {
 lean_dec_ref(x_74);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 6, 1);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_76);
lean_ctor_set(x_82, 1, x_77);
lean_ctor_set(x_82, 2, x_78);
lean_ctor_set(x_82, 3, x_79);
lean_ctor_set(x_82, 4, x_70);
lean_ctor_set(x_82, 5, x_4);
lean_ctor_set_uint8(x_82, sizeof(void*)*6, x_80);
x_83 = lean_st_ref_set(x_9, x_82, x_75);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_box(0);
x_86 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(x_1, x_85, x_8, x_9, x_10, x_11, x_84);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
x_87 = lean_ctor_get(x_15, 1);
lean_inc(x_87);
lean_dec(x_15);
x_88 = lean_st_ref_get(x_11, x_87);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_st_ref_take(x_9, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = !lean_is_exclusive(x_91);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_91, 5);
lean_dec(x_94);
x_95 = lean_ctor_get(x_91, 4);
lean_dec(x_95);
lean_ctor_set(x_91, 5, x_6);
lean_ctor_set(x_91, 4, x_5);
x_96 = lean_st_ref_set(x_9, x_91, x_92);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_box(0);
x_99 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(x_1, x_98, x_8, x_9, x_10, x_11, x_97);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_100 = lean_ctor_get(x_91, 0);
x_101 = lean_ctor_get(x_91, 1);
x_102 = lean_ctor_get(x_91, 2);
x_103 = lean_ctor_get(x_91, 3);
x_104 = lean_ctor_get_uint8(x_91, sizeof(void*)*6);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_91);
x_105 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_105, 0, x_100);
lean_ctor_set(x_105, 1, x_101);
lean_ctor_set(x_105, 2, x_102);
lean_ctor_set(x_105, 3, x_103);
lean_ctor_set(x_105, 4, x_5);
lean_ctor_set(x_105, 5, x_6);
lean_ctor_set_uint8(x_105, sizeof(void*)*6, x_104);
x_106 = lean_st_ref_set(x_9, x_105, x_92);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_box(0);
x_109 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(x_1, x_108, x_8, x_9, x_10, x_11, x_107);
return x_109;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_maxPrec;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesized: ");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_42; lean_object* x_43; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_st_ref_get(x_10, x_11);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 3);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_ctor_get_uint8(x_57, sizeof(void*)*1);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
x_60 = 0;
x_42 = x_60;
x_43 = x_59;
goto block_54;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_dec(x_55);
lean_inc(x_4);
x_62 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_4, x_7, x_8, x_9, x_10, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_unbox(x_63);
lean_dec(x_63);
x_42 = x_65;
x_43 = x_64;
goto block_54;
}
block_41:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_13 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5(x_5, x_7, x_8, x_9, x_10, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_8, x_9, x_10, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_10, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_take(x_8, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_20, 4);
lean_dec(x_23);
x_24 = lean_ctor_get(x_20, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_20, 1);
lean_dec(x_25);
x_26 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1;
lean_ctor_set(x_20, 4, x_2);
lean_ctor_set(x_20, 2, x_1);
lean_ctor_set(x_20, 1, x_26);
x_27 = lean_st_ref_set(x_8, x_20, x_21);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = lean_apply_6(x_3, x_29, x_7, x_8, x_9, x_10, x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 3);
x_33 = lean_ctor_get(x_20, 5);
x_34 = lean_ctor_get_uint8(x_20, sizeof(void*)*6);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_35 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1;
x_36 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_1);
lean_ctor_set(x_36, 3, x_32);
lean_ctor_set(x_36, 4, x_2);
lean_ctor_set(x_36, 5, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*6, x_34);
x_37 = lean_st_ref_set(x_8, x_36, x_21);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_box(0);
x_40 = lean_apply_6(x_3, x_39, x_7, x_8, x_9, x_10, x_38);
return x_40;
}
}
block_54:
{
if (x_42 == 0)
{
lean_dec(x_4);
x_12 = x_43;
goto block_41;
}
else
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = 0;
x_45 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_46 = l_Lean_Syntax_formatStxAux(x_2, x_44, x_45, x_5);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__3;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_KernelException_toMessageData___closed__15;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_4, x_51, x_7, x_8, x_9, x_10, x_43);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_12 = x_53;
goto block_41;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Syntax_getTailInfo(x_5);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = l_Substring_splitOn_loop___closed__2;
lean_ctor_set(x_13, 0, x_16);
x_17 = l_Lean_Syntax_setTailInfo(x_6, x_13);
x_18 = lean_box(0);
x_19 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3(x_1, x_2, x_3, x_4, x_17, x_18, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_13, 1);
x_21 = lean_ctor_get(x_13, 2);
x_22 = lean_ctor_get(x_13, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_23 = l_Substring_splitOn_loop___closed__2;
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
x_25 = l_Lean_Syntax_setTailInfo(x_6, x_24);
x_26 = lean_box(0);
x_27 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3(x_1, x_2, x_3, x_4, x_25, x_26, x_8, x_9, x_10, x_11, x_12);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_13);
x_28 = lean_box(0);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3(x_1, x_2, x_3, x_4, x_6, x_28, x_8, x_9, x_10, x_11, x_12);
return x_29;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_6);
x_13 = lean_apply_1(x_1, x_6);
x_14 = l_Lean_Syntax_getHeadInfo(x_6);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 2);
lean_dec(x_16);
x_17 = l_Substring_splitOn_loop___closed__2;
lean_ctor_set(x_14, 2, x_17);
x_18 = l_Lean_Syntax_setHeadInfo(x_13, x_14);
x_19 = lean_box(0);
x_20 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4(x_2, x_3, x_4, x_5, x_6, x_18, x_19, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
x_23 = lean_ctor_get(x_14, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_24 = l_Substring_splitOn_loop___closed__2;
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_23);
x_26 = l_Lean_Syntax_setHeadInfo(x_13, x_25);
x_27 = lean_box(0);
x_28 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4(x_2, x_3, x_4, x_5, x_6, x_26, x_27, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_14);
x_29 = lean_box(0);
x_30 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4(x_2, x_3, x_4, x_5, x_6, x_13, x_29, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_30;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Syntax_getTailInfo(x_6);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 2);
lean_dec(x_15);
x_16 = l_Substring_splitOn_loop___closed__2;
lean_ctor_set(x_13, 2, x_16);
x_17 = l_Lean_Syntax_setTailInfo(x_6, x_13);
x_18 = lean_box(0);
x_19 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
x_22 = lean_ctor_get(x_13, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_23 = l_Substring_splitOn_loop___closed__2;
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_22);
x_25 = l_Lean_Syntax_setTailInfo(x_6, x_24);
x_26 = lean_box(0);
x_27 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5(x_1, x_2, x_3, x_4, x_5, x_25, x_26, x_8, x_9, x_10, x_11, x_12);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_13);
x_28 = lean_box(0);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_28, x_8, x_9, x_10, x_11, x_12);
return x_29;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Syntax_getHeadInfo(x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = l_Substring_splitOn_loop___closed__2;
lean_ctor_set(x_15, 0, x_18);
x_19 = l_Lean_Syntax_setHeadInfo(x_13, x_15);
x_20 = lean_box(0);
x_21 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__6(x_1, x_2, x_3, x_4, x_5, x_19, x_20, x_7, x_8, x_9, x_10, x_14);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_15, 1);
x_23 = lean_ctor_get(x_15, 2);
x_24 = lean_ctor_get(x_15, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_25 = l_Substring_splitOn_loop___closed__2;
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_24);
x_27 = l_Lean_Syntax_setHeadInfo(x_13, x_26);
x_28 = lean_box(0);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__6(x_1, x_2, x_3, x_4, x_5, x_27, x_28, x_7, x_8, x_9, x_10, x_14);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_15);
x_30 = lean_box(0);
x_31 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__6(x_1, x_2, x_3, x_4, x_5, x_13, x_30, x_7, x_8, x_9, x_10, x_14);
return x_31;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesize");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("visited a syntax tree without precedences?!");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("...precedences are {prec} >? {minPrec}");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Format_join___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__8;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__9;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term_x5b___x5d___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" <=? ");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesizing (cont := ");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_prec_x28___x29___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_11 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg(x_7, x_8, x_9, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_9, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_7, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_143; lean_object* x_144; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_20, 2);
x_25 = lean_ctor_get(x_20, 3);
x_26 = lean_ctor_get(x_20, 4);
x_27 = lean_ctor_get(x_20, 5);
x_28 = lean_ctor_get_uint8(x_20, sizeof(void*)*6);
x_29 = lean_box(0);
x_30 = lean_box(0);
x_31 = 0;
lean_ctor_set(x_20, 5, x_30);
lean_ctor_set(x_20, 4, x_29);
lean_ctor_set(x_20, 3, x_29);
lean_ctor_set(x_20, 2, x_30);
lean_ctor_set(x_20, 1, x_29);
lean_ctor_set_uint8(x_20, sizeof(void*)*6, x_31);
x_32 = lean_st_ref_get(x_9, x_21);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_st_ref_set(x_7, x_20, x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_184 = lean_st_ref_get(x_9, x_35);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_185, 3);
lean_inc(x_186);
lean_dec(x_185);
x_187 = lean_ctor_get_uint8(x_186, sizeof(void*)*1);
lean_dec(x_186);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_184, 1);
lean_inc(x_188);
lean_dec(x_184);
x_143 = x_31;
x_144 = x_188;
goto block_183;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_189 = lean_ctor_get(x_184, 1);
lean_inc(x_189);
lean_dec(x_184);
x_190 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_191 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_190, x_6, x_7, x_8, x_9, x_189);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_unbox(x_192);
lean_dec(x_192);
x_143 = x_194;
x_144 = x_193;
goto block_183;
}
block_142:
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 3);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_36);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = lean_st_ref_get(x_9, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
lean_dec(x_41);
if (x_42 == 0)
{
uint8_t x_43; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_39, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_39, 0, x_45);
return x_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_dec(x_39);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_39, 1);
lean_inc(x_49);
lean_dec(x_39);
x_50 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_51 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_50, x_6, x_7, x_8, x_9, x_49);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
uint8_t x_54; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_51, 0);
lean_dec(x_55);
x_56 = lean_box(0);
lean_ctor_set(x_51, 0, x_56);
return x_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_dec(x_51);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_dec(x_51);
x_61 = l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_12);
x_62 = lean_box(1);
x_63 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lean_KernelException_toMessageData___closed__15;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_50, x_68, x_6, x_7, x_8, x_9, x_60);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_106; lean_object* x_107; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
lean_dec(x_12);
x_70 = lean_ctor_get(x_36, 4);
lean_inc(x_70);
x_71 = lean_ctor_get(x_36, 5);
lean_inc(x_71);
lean_dec(x_36);
x_72 = lean_ctor_get(x_38, 0);
lean_inc(x_72);
lean_dec(x_38);
x_131 = lean_st_ref_get(x_9, x_37);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_132, 3);
lean_inc(x_133);
lean_dec(x_132);
x_134 = lean_ctor_get_uint8(x_133, sizeof(void*)*1);
lean_dec(x_133);
if (x_134 == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
lean_dec(x_131);
x_106 = x_31;
x_107 = x_135;
goto block_130;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_136 = lean_ctor_get(x_131, 1);
lean_inc(x_136);
lean_dec(x_131);
x_137 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_138 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_137, x_6, x_7, x_8, x_9, x_136);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_unbox(x_139);
lean_dec(x_139);
x_106 = x_141;
x_107 = x_140;
goto block_130;
}
block_105:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_88; 
x_74 = lean_box(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_25);
x_75 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___boxed), 12, 6);
lean_closure_set(x_75, 0, x_25);
lean_closure_set(x_75, 1, x_74);
lean_closure_set(x_75, 2, x_4);
lean_closure_set(x_75, 3, x_1);
lean_closure_set(x_75, 4, x_26);
lean_closure_set(x_75, 5, x_27);
x_88 = lean_nat_dec_lt(x_72, x_4);
lean_dec(x_72);
if (x_88 == 0)
{
if (x_2 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_75);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_3);
x_89 = lean_box(0);
x_90 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_25, x_28, x_4, x_1, x_26, x_27, x_89, x_6, x_7, x_8, x_9, x_73);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_90;
}
else
{
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_75);
lean_dec(x_71);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_3);
x_91 = lean_box(0);
x_92 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_25, x_28, x_4, x_1, x_26, x_27, x_91, x_6, x_7, x_8, x_9, x_73);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_92;
}
else
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_75);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_3);
x_93 = lean_box(0);
x_94 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_25, x_28, x_4, x_1, x_26, x_27, x_93, x_6, x_7, x_8, x_9, x_73);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_70, 0);
lean_inc(x_95);
lean_dec(x_70);
x_96 = lean_ctor_get(x_23, 0);
lean_inc(x_96);
lean_dec(x_23);
x_97 = lean_name_eq(x_71, x_24);
lean_dec(x_24);
lean_dec(x_71);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_75);
lean_dec(x_15);
lean_dec(x_3);
x_98 = lean_box(0);
x_99 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_25, x_28, x_4, x_1, x_26, x_27, x_98, x_6, x_7, x_8, x_9, x_73);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_99;
}
else
{
uint8_t x_100; 
x_100 = lean_nat_dec_le(x_95, x_96);
lean_dec(x_96);
lean_dec(x_95);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_75);
lean_dec(x_15);
lean_dec(x_3);
x_101 = lean_box(0);
x_102 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_25, x_28, x_4, x_1, x_26, x_27, x_101, x_6, x_7, x_8, x_9, x_73);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_102;
}
else
{
lean_object* x_103; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_4);
x_103 = lean_box(0);
x_76 = x_103;
goto block_87;
}
}
}
}
}
}
else
{
lean_object* x_104; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_4);
x_104 = lean_box(0);
x_76 = x_104;
goto block_87;
}
block_87:
{
lean_object* x_77; uint8_t x_78; 
lean_dec(x_76);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_nat_dec_lt(x_77, x_15);
lean_dec(x_15);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_80 = lean_box(0);
x_81 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__7(x_3, x_1, x_29, x_75, x_79, x_80, x_6, x_7, x_8, x_9, x_73);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___rarg(x_7, x_8, x_9, x_73);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_86 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__7(x_3, x_1, x_29, x_75, x_85, x_83, x_6, x_7, x_8, x_9, x_84);
lean_dec(x_83);
return x_86;
}
}
}
block_130:
{
if (x_106 == 0)
{
x_73 = x_107;
goto block_105;
}
else
{
if (x_2 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_109 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
x_110 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_108, x_109, x_6, x_7, x_8, x_9, x_107);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_73 = x_111;
goto block_105;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_inc(x_71);
lean_inc(x_70);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_70);
lean_ctor_set(x_112, 1, x_71);
x_113 = l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7(x_112);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__11;
x_116 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_118 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
lean_inc(x_24);
lean_inc(x_23);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_23);
lean_ctor_set(x_119, 1, x_24);
x_120 = l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7(x_119);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_KernelException_toMessageData___closed__15;
x_124 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__8;
x_126 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_128 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_127, x_126, x_6, x_7, x_8, x_9, x_107);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_73 = x_129;
goto block_105;
}
}
}
}
}
block_183:
{
if (x_143 == 0)
{
lean_object* x_145; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_145 = lean_apply_5(x_5, x_6, x_7, x_8, x_9, x_144);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_st_ref_get(x_9, x_146);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_149 = lean_st_ref_get(x_7, x_148);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_36 = x_150;
x_37 = x_151;
goto block_142;
}
else
{
uint8_t x_152; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_145);
if (x_152 == 0)
{
return x_145;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_145, 0);
x_154 = lean_ctor_get(x_145, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_145);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_inc(x_24);
lean_inc(x_23);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_23);
lean_ctor_set(x_156, 1, x_24);
x_157 = l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7(x_156);
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__15;
x_160 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__16;
x_162 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
lean_inc(x_12);
x_163 = l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_12);
x_164 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_165 = l_Lean_indentD(x_164);
x_166 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_166, 0, x_162);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_KernelException_toMessageData___closed__15;
x_168 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_170 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_169, x_168, x_6, x_7, x_8, x_9, x_144);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_172 = lean_apply_5(x_5, x_6, x_7, x_8, x_9, x_171);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec(x_172);
x_174 = lean_st_ref_get(x_9, x_173);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_176 = lean_st_ref_get(x_7, x_175);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_36 = x_177;
x_37 = x_178;
goto block_142;
}
else
{
uint8_t x_179; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_179 = !lean_is_exclusive(x_172);
if (x_179 == 0)
{
return x_172;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_172, 0);
x_181 = lean_ctor_get(x_172, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_172);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_313; lean_object* x_314; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_195 = lean_ctor_get(x_20, 0);
x_196 = lean_ctor_get(x_20, 1);
x_197 = lean_ctor_get(x_20, 2);
x_198 = lean_ctor_get(x_20, 3);
x_199 = lean_ctor_get(x_20, 4);
x_200 = lean_ctor_get(x_20, 5);
x_201 = lean_ctor_get_uint8(x_20, sizeof(void*)*6);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_20);
x_202 = lean_box(0);
x_203 = lean_box(0);
x_204 = 0;
x_205 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_205, 0, x_195);
lean_ctor_set(x_205, 1, x_202);
lean_ctor_set(x_205, 2, x_203);
lean_ctor_set(x_205, 3, x_202);
lean_ctor_set(x_205, 4, x_202);
lean_ctor_set(x_205, 5, x_203);
lean_ctor_set_uint8(x_205, sizeof(void*)*6, x_204);
x_206 = lean_st_ref_get(x_9, x_21);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec(x_206);
x_208 = lean_st_ref_set(x_7, x_205, x_207);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec(x_208);
x_354 = lean_st_ref_get(x_9, x_209);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_355, 3);
lean_inc(x_356);
lean_dec(x_355);
x_357 = lean_ctor_get_uint8(x_356, sizeof(void*)*1);
lean_dec(x_356);
if (x_357 == 0)
{
lean_object* x_358; 
x_358 = lean_ctor_get(x_354, 1);
lean_inc(x_358);
lean_dec(x_354);
x_313 = x_204;
x_314 = x_358;
goto block_353;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; 
x_359 = lean_ctor_get(x_354, 1);
lean_inc(x_359);
lean_dec(x_354);
x_360 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_361 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_360, x_6, x_7, x_8, x_9, x_359);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec(x_361);
x_364 = lean_unbox(x_362);
lean_dec(x_362);
x_313 = x_364;
x_314 = x_363;
goto block_353;
}
block_312:
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_210, 3);
lean_inc(x_212);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
lean_dec(x_210);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_213 = lean_st_ref_get(x_9, x_211);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_214, 3);
lean_inc(x_215);
lean_dec(x_214);
x_216 = lean_ctor_get_uint8(x_215, sizeof(void*)*1);
lean_dec(x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_217 = lean_ctor_get(x_213, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_218 = x_213;
} else {
 lean_dec_ref(x_213);
 x_218 = lean_box(0);
}
x_219 = lean_box(0);
if (lean_is_scalar(x_218)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_218;
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_217);
return x_220;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_221 = lean_ctor_get(x_213, 1);
lean_inc(x_221);
lean_dec(x_213);
x_222 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_223 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_222, x_6, x_7, x_8, x_9, x_221);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_unbox(x_224);
lean_dec(x_224);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_226 = lean_ctor_get(x_223, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_227 = x_223;
} else {
 lean_dec_ref(x_223);
 x_227 = lean_box(0);
}
x_228 = lean_box(0);
if (lean_is_scalar(x_227)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_227;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_226);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_230 = lean_ctor_get(x_223, 1);
lean_inc(x_230);
lean_dec(x_223);
x_231 = l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_12);
x_232 = lean_box(1);
x_233 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
x_234 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_234, 0, x_233);
x_235 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_236 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_234);
x_237 = l_Lean_KernelException_toMessageData___closed__15;
x_238 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
x_239 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_222, x_238, x_6, x_7, x_8, x_9, x_230);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_239;
}
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_276; lean_object* x_277; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
lean_dec(x_12);
x_240 = lean_ctor_get(x_210, 4);
lean_inc(x_240);
x_241 = lean_ctor_get(x_210, 5);
lean_inc(x_241);
lean_dec(x_210);
x_242 = lean_ctor_get(x_212, 0);
lean_inc(x_242);
lean_dec(x_212);
x_301 = lean_st_ref_get(x_9, x_211);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_302, 3);
lean_inc(x_303);
lean_dec(x_302);
x_304 = lean_ctor_get_uint8(x_303, sizeof(void*)*1);
lean_dec(x_303);
if (x_304 == 0)
{
lean_object* x_305; 
x_305 = lean_ctor_get(x_301, 1);
lean_inc(x_305);
lean_dec(x_301);
x_276 = x_204;
x_277 = x_305;
goto block_300;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; 
x_306 = lean_ctor_get(x_301, 1);
lean_inc(x_306);
lean_dec(x_301);
x_307 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_308 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_307, x_6, x_7, x_8, x_9, x_306);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
x_311 = lean_unbox(x_309);
lean_dec(x_309);
x_276 = x_311;
x_277 = x_310;
goto block_300;
}
block_275:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_258; 
x_244 = lean_box(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_198);
x_245 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___boxed), 12, 6);
lean_closure_set(x_245, 0, x_198);
lean_closure_set(x_245, 1, x_244);
lean_closure_set(x_245, 2, x_4);
lean_closure_set(x_245, 3, x_1);
lean_closure_set(x_245, 4, x_199);
lean_closure_set(x_245, 5, x_200);
x_258 = lean_nat_dec_lt(x_242, x_4);
lean_dec(x_242);
if (x_258 == 0)
{
if (x_2 == 0)
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_245);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_15);
lean_dec(x_3);
x_259 = lean_box(0);
x_260 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_198, x_201, x_4, x_1, x_199, x_200, x_259, x_6, x_7, x_8, x_9, x_243);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_260;
}
else
{
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_261; lean_object* x_262; 
lean_dec(x_245);
lean_dec(x_241);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_15);
lean_dec(x_3);
x_261 = lean_box(0);
x_262 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_198, x_201, x_4, x_1, x_199, x_200, x_261, x_6, x_7, x_8, x_9, x_243);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_262;
}
else
{
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_245);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_197);
lean_dec(x_15);
lean_dec(x_3);
x_263 = lean_box(0);
x_264 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_198, x_201, x_4, x_1, x_199, x_200, x_263, x_6, x_7, x_8, x_9, x_243);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_264;
}
else
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_265 = lean_ctor_get(x_240, 0);
lean_inc(x_265);
lean_dec(x_240);
x_266 = lean_ctor_get(x_196, 0);
lean_inc(x_266);
lean_dec(x_196);
x_267 = lean_name_eq(x_241, x_197);
lean_dec(x_197);
lean_dec(x_241);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; 
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_245);
lean_dec(x_15);
lean_dec(x_3);
x_268 = lean_box(0);
x_269 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_198, x_201, x_4, x_1, x_199, x_200, x_268, x_6, x_7, x_8, x_9, x_243);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_269;
}
else
{
uint8_t x_270; 
x_270 = lean_nat_dec_le(x_265, x_266);
lean_dec(x_266);
lean_dec(x_265);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; 
lean_dec(x_245);
lean_dec(x_15);
lean_dec(x_3);
x_271 = lean_box(0);
x_272 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_198, x_201, x_4, x_1, x_199, x_200, x_271, x_6, x_7, x_8, x_9, x_243);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_272;
}
else
{
lean_object* x_273; 
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_4);
x_273 = lean_box(0);
x_246 = x_273;
goto block_257;
}
}
}
}
}
}
else
{
lean_object* x_274; 
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_4);
x_274 = lean_box(0);
x_246 = x_274;
goto block_257;
}
block_257:
{
lean_object* x_247; uint8_t x_248; 
lean_dec(x_246);
x_247 = lean_unsigned_to_nat(0u);
x_248 = lean_nat_dec_lt(x_247, x_15);
lean_dec(x_15);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_250 = lean_box(0);
x_251 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__7(x_3, x_1, x_202, x_245, x_249, x_250, x_6, x_7, x_8, x_9, x_243);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___rarg(x_7, x_8, x_9, x_243);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_256 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__7(x_3, x_1, x_202, x_245, x_255, x_253, x_6, x_7, x_8, x_9, x_254);
lean_dec(x_253);
return x_256;
}
}
}
block_300:
{
if (x_276 == 0)
{
x_243 = x_277;
goto block_275;
}
else
{
if (x_2 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_278 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_279 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
x_280 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_278, x_279, x_6, x_7, x_8, x_9, x_277);
x_281 = lean_ctor_get(x_280, 1);
lean_inc(x_281);
lean_dec(x_280);
x_243 = x_281;
goto block_275;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_inc(x_241);
lean_inc(x_240);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_240);
lean_ctor_set(x_282, 1, x_241);
x_283 = l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7(x_282);
x_284 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_284, 0, x_283);
x_285 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__11;
x_286 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_284);
x_287 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_288 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
lean_inc(x_197);
lean_inc(x_196);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_196);
lean_ctor_set(x_289, 1, x_197);
x_290 = l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7(x_289);
x_291 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_291, 0, x_290);
x_292 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_292, 0, x_288);
lean_ctor_set(x_292, 1, x_291);
x_293 = l_Lean_KernelException_toMessageData___closed__15;
x_294 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
x_295 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__8;
x_296 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_294);
x_297 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_298 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_297, x_296, x_6, x_7, x_8, x_9, x_277);
x_299 = lean_ctor_get(x_298, 1);
lean_inc(x_299);
lean_dec(x_298);
x_243 = x_299;
goto block_275;
}
}
}
}
}
block_353:
{
if (x_313 == 0)
{
lean_object* x_315; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_315 = lean_apply_5(x_5, x_6, x_7, x_8, x_9, x_314);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
lean_dec(x_315);
x_317 = lean_st_ref_get(x_9, x_316);
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
lean_dec(x_317);
x_319 = lean_st_ref_get(x_7, x_318);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
lean_dec(x_319);
x_210 = x_320;
x_211 = x_321;
goto block_312;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_322 = lean_ctor_get(x_315, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_315, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_324 = x_315;
} else {
 lean_dec_ref(x_315);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(1, 2, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_322);
lean_ctor_set(x_325, 1, x_323);
return x_325;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_inc(x_197);
lean_inc(x_196);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_196);
lean_ctor_set(x_326, 1, x_197);
x_327 = l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7(x_326);
x_328 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_328, 0, x_327);
x_329 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__15;
x_330 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_328);
x_331 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__16;
x_332 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
lean_inc(x_12);
x_333 = l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_12);
x_334 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_334, 0, x_333);
x_335 = l_Lean_indentD(x_334);
x_336 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_336, 0, x_332);
lean_ctor_set(x_336, 1, x_335);
x_337 = l_Lean_KernelException_toMessageData___closed__15;
x_338 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
x_339 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_340 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_339, x_338, x_6, x_7, x_8, x_9, x_314);
x_341 = lean_ctor_get(x_340, 1);
lean_inc(x_341);
lean_dec(x_340);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_342 = lean_apply_5(x_5, x_6, x_7, x_8, x_9, x_341);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_343 = lean_ctor_get(x_342, 1);
lean_inc(x_343);
lean_dec(x_342);
x_344 = lean_st_ref_get(x_9, x_343);
x_345 = lean_ctor_get(x_344, 1);
lean_inc(x_345);
lean_dec(x_344);
x_346 = lean_st_ref_get(x_7, x_345);
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
x_210 = x_347;
x_211 = x_348;
goto block_312;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_349 = lean_ctor_get(x_342, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_342, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_351 = x_342;
} else {
 lean_dec_ref(x_342);
 x_351 = lean_box(0);
}
if (lean_is_scalar(x_351)) {
 x_352 = lean_alloc_ctor(1, 2, 0);
} else {
 x_352 = x_351;
}
lean_ctor_set(x_352, 0, x_349);
lean_ctor_set(x_352, 1, x_350);
return x_352;
}
}
}
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_14;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_5);
return x_13;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_13;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_13;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_st_ref_take(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_8, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_dec(x_12);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = 1;
lean_ctor_set(x_8, 2, x_14);
lean_ctor_set(x_8, 1, x_13);
lean_ctor_set_uint8(x_8, sizeof(void*)*6, x_15);
x_16 = lean_st_ref_set(x_1, x_8, x_9);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_1, x_2, x_3, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 3);
x_21 = lean_ctor_get(x_8, 4);
x_22 = lean_ctor_get(x_8, 5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = 1;
x_26 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_20);
lean_ctor_set(x_26, 4, x_21);
lean_ctor_set(x_26, 5, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*6, x_25);
x_27 = lean_st_ref_set(x_1, x_26, x_9);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_1, x_2, x_3, x_28);
return x_29;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_visitToken(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_6, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_17, 1);
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
x_27 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_28 = lean_nat_dec_eq(x_27, x_26);
lean_dec(x_26);
if (x_28 == 0)
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_17);
lean_dec(x_18);
x_29 = lean_st_ref_get(x_6, x_24);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_set(x_4, x_15, x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_dec(x_17);
x_35 = lean_ctor_get(x_18, 0);
lean_inc(x_35);
x_36 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_37 = lean_nat_dec_eq(x_36, x_35);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_18);
x_39 = lean_st_ref_get(x_6, x_34);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_st_ref_set(x_4, x_15, x_40);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_42);
return x_43;
}
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_mk_antiquot_parenthesizer(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_3(x_1, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_liftCoreM___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_liftCoreM___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_pretty_printer_parenthesizer_interpret_parser_descr(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr_x27___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Syntax_getKind___closed__2;
x_8 = lean_name_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_10 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__1;
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_PrettyPrinter_runForNodeKind___rarg(x_9, x_1, x_10, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_5(x_12, x_2, x_3, x_4, x_5, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Syntax_isAntiquotSuffixSplice(x_9);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___rarg___lambda__1), 7, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_1);
x_14 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_13, x_3, x_4, x_5, x_6, x_10);
return x_14;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_isTokenAntiquot(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_1, x_2, x_3, x_4, x_5, x_9);
return x_12;
}
}
}
lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_2, x_10);
lean_dec(x_2);
x_12 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_4, x_5, x_6, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Syntax_getKind(x_13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(x_15, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_2 = x_11;
x_7 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
return x_24;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_11, 2);
lean_dec(x_14);
lean_ctor_set(x_11, 2, x_1);
x_15 = lean_st_ref_set(x_4, x_11, x_12);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
x_24 = lean_ctor_get(x_11, 3);
x_25 = lean_ctor_get(x_11, 4);
x_26 = lean_ctor_get(x_11, 5);
x_27 = lean_ctor_get_uint8(x_11, sizeof(void*)*6);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_28 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_1);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_28, 4, x_25);
lean_ctor_set(x_28, 5, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*6, x_27);
x_29 = lean_st_ref_set(x_4, x_28, x_12);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = l_Lean_Syntax_getKind(x_9);
x_12 = l_Lean_choiceKind___closed__2;
x_13 = lean_name_eq(x_11, x_12);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
x_14 = 1;
lean_inc(x_1);
x_15 = l_Lean_Name_toString(x_1, x_14);
x_16 = lean_box(0);
x_17 = lean_box(x_14);
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed), 8, 3);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_16);
lean_closure_set(x_18, 2, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe), 6, 1);
lean_closure_set(x_19, 0, x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_20 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_18, x_19, x_1, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_1);
x_23 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lambda__1(x_1, x_21, x_1, x_4, x_5, x_6, x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_21);
lean_dec(x_1);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
x_28 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_29 = lean_array_get_size(x_28);
lean_dec(x_28);
lean_inc(x_29);
x_30 = lean_alloc_closure((void*)(l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1___boxed), 7, 2);
lean_closure_set(x_30, 0, x_29);
lean_closure_set(x_30, 1, x_29);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_31 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_30, x_1, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_1);
x_34 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lambda__1(x_1, x_32, x_1, x_4, x_5, x_6, x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_32);
lean_dec(x_1);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_PrettyPrinter_categoryParenthesizerAttribute;
x_13 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_12, x_11, x_1);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_apply_6(x_15, x_2, x_3, x_4, x_5, x_6, x_10);
return x_16;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParserOfStack_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_13, 2);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(x_16);
lean_dec(x_16);
x_18 = lean_nat_sub(x_17, x_1);
lean_dec(x_17);
x_19 = l_Lean_Syntax_getArg(x_15, x_18);
lean_dec(x_18);
lean_dec(x_15);
x_20 = l_Lean_Syntax_getId(x_19);
lean_dec(x_19);
x_21 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_20, x_2, x_3, x_4, x_5, x_6, x_12);
return x_21;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParserOfStack_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_categoryParserOfStack_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_13, 2);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(x_16);
lean_dec(x_16);
x_18 = lean_nat_sub(x_17, x_1);
lean_dec(x_17);
x_19 = l_Lean_Syntax_getArg(x_15, x_18);
lean_dec(x_18);
lean_dec(x_15);
x_20 = l_Lean_Syntax_getKind(x_19);
x_21 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(x_20, x_3, x_4, x_5, x_6, x_12);
return x_21;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_5 = l_prec_x28___x29___closed__3;
lean_inc(x_2);
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_myMacro____x40_Init_Notation___hyg_1318____closed__8;
x_8 = lean_array_push(x_7, x_1);
x_9 = l_myMacro____x40_Init_Notation___hyg_1318____closed__9;
x_10 = lean_array_push(x_8, x_9);
x_11 = l_Lean_nullKind___closed__2;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_prec_x28___x29___closed__7;
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_unexpand____x40_Init_Notation___hyg_1981____closed__1;
x_16 = lean_array_push(x_15, x_6);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_14);
x_19 = l_myMacro____x40_Init_Notation___hyg_12862____closed__8;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Level_PP_Result_quote___closed__1;
x_4 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Lean_Unhygienic_run___rarg(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__2), 1, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getKind(x_8);
x_11 = l_Lean_nullKind;
x_12 = lean_name_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = l_term___u2218_____closed__6;
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed), 7, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_1);
x_15 = 1;
x_16 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1;
x_17 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_13, x_15, x_16, x_1, x_14, x_2, x_3, x_4, x_5, x_9);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg(x_9);
return x_18;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer), 6, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_categoryParenthesizerAttribute;
x_3 = l_term___u2218_____closed__6;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = l_prec_x28___x29___closed__3;
lean_inc(x_2);
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_myMacro____x40_Init_Notation___hyg_71____closed__2;
x_8 = lean_array_push(x_7, x_1);
x_9 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_15488____closed__3;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_prec_x28___x29___closed__7;
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_unexpand____x40_Init_Notation___hyg_1981____closed__1;
x_14 = lean_array_push(x_13, x_6);
x_15 = lean_array_push(x_14, x_10);
x_16 = lean_array_push(x_15, x_12);
x_17 = l_Lean_Parser_Tactic_paren___closed__1;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Level_PP_Result_quote___closed__1;
x_4 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Lean_Unhygienic_run___rarg(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__2), 1, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Parser_Tactic_tactic___x3c_x3b_x3e_____closed__6;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = 0;
x_10 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1;
x_11 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_7, x_9, x_10, x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer), 6, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_categoryParenthesizerAttribute;
x_3 = l_Lean_Parser_Tactic_tactic___x3c_x3b_x3e_____closed__6;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_PP_Result_quote___lambda__4___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Level_PP_Result_quote___closed__1;
x_4 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Lean_Unhygienic_run___rarg(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("level");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = 0;
x_10 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3;
x_11 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_7, x_9, x_10, x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer), 6, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_categoryParenthesizerAttribute;
x_3 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___rarg), 1, 0);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_atomic_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___rarg), 1, 0);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("backtrack");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected node kind '");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', expected '");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Syntax_getKind(x_9);
x_12 = lean_name_eq(x_1, x_11);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_2);
x_38 = lean_st_ref_get(x_6, x_10);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 3);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get_uint8(x_40, sizeof(void*)*1);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = 0;
x_13 = x_43;
x_14 = x_42;
goto block_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_46 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_45, x_3, x_4, x_5, x_6, x_44);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_unbox(x_47);
lean_dec(x_47);
x_13 = x_49;
x_14 = x_48;
goto block_37;
}
block_37:
{
if (x_13 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg(x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_20 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_20, 0, x_11);
x_21 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__4;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__6;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_25, 0, x_1);
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_KernelException_toMessageData___closed__3;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_30 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_29, x_28, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg(x_31);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
lean_object* x_50; 
lean_dec(x_11);
lean_dec(x_1);
x_50 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_2, x_3, x_4, x_5, x_6, x_10);
return x_50;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_maxPrec;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(x_2, x_4, x_5, x_6, x_7, x_10);
lean_dec(x_6);
lean_dec(x_4);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_7, x_12);
lean_dec(x_7);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_take(x_5, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_16, 1);
lean_dec(x_19);
x_20 = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___closed__1;
x_21 = l_Nat_min(x_20, x_2);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_16, 1, x_22);
x_23 = lean_st_ref_set(x_5, x_16, x_17);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 2);
x_32 = lean_ctor_get(x_16, 3);
x_33 = lean_ctor_get(x_16, 4);
x_34 = lean_ctor_get(x_16, 5);
x_35 = lean_ctor_get_uint8(x_16, sizeof(void*)*6);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_36 = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___closed__1;
x_37 = l_Nat_min(x_36, x_2);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_31);
lean_ctor_set(x_39, 3, x_32);
lean_ctor_set(x_39, 4, x_33);
lean_ctor_set(x_39, 5, x_34);
lean_ctor_set_uint8(x_39, sizeof(void*)*6, x_35);
x_40 = lean_st_ref_set(x_5, x_39, x_17);
lean_dec(x_5);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = lean_box(0);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_9);
if (x_45 == 0)
{
return x_9;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_9, 0);
x_47 = lean_ctor_get(x_9, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_9);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(x_1, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_6, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_take(x_4, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_13, 2);
lean_dec(x_16);
lean_inc(x_3);
lean_ctor_set(x_13, 2, x_3);
x_17 = lean_st_ref_set(x_4, x_13, x_14);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_20 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_3, x_19, x_3, x_4, x_5, x_6, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
x_23 = lean_ctor_get(x_13, 3);
x_24 = lean_ctor_get(x_13, 4);
x_25 = lean_ctor_get(x_13, 5);
x_26 = lean_ctor_get_uint8(x_13, sizeof(void*)*6);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
lean_inc(x_3);
x_27 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_3);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set(x_27, 5, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*6, x_26);
x_28 = lean_st_ref_set(x_4, x_27, x_14);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_31 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_3, x_30, x_3, x_4, x_5, x_6, x_29);
return x_31;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___boxed), 7, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1___rarg), 7, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Syntax_getKind(x_11);
x_14 = lean_name_eq(x_1, x_13);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_4);
lean_dec(x_2);
x_40 = lean_st_ref_get(x_8, x_12);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 3);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get_uint8(x_42, sizeof(void*)*1);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = 0;
x_15 = x_45;
x_16 = x_44;
goto block_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_dec(x_40);
x_47 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_48 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_47, x_5, x_6, x_7, x_8, x_46);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unbox(x_49);
lean_dec(x_49);
x_15 = x_51;
x_16 = x_50;
goto block_39;
}
block_39:
{
if (x_15 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_17 = l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg(x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_13);
x_23 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__6;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_27, 0, x_1);
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_KernelException_toMessageData___closed__3;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_32 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_31, x_30, x_5, x_6, x_7, x_8, x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg(x_33);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_13);
lean_dec(x_1);
x_52 = lean_box(0);
x_53 = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__2(x_2, x_4, x_52, x_5, x_6, x_7, x_8, x_12);
return x_53;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = lean_apply_5(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_3 = x_12;
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_8);
return x_21;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_11 = lean_array_get_size(x_10);
lean_dec(x_10);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer___spec__1___boxed), 8, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_11);
x_13 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_12, x_2, x_3, x_4, x_5, x_9);
return x_13;
}
}
lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_many1NoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_many1Unbox_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getKind(x_8);
x_11 = l_Lean_nullKind;
x_12 = lean_name_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_9);
return x_14;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_optionalNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_List_forM___at_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_mod(x_11, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_inc(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_3 = x_12;
x_8 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = lean_apply_5(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_3 = x_12;
x_8 = x_25;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
x_13 = l_List_range(x_12);
x_14 = l_List_reverse___rarg(x_13);
x_15 = lean_alloc_closure((void*)(l_List_forM___at_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer___spec__1___boxed), 8, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_14);
x_16 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_15, x_3, x_4, x_5, x_6, x_10);
return x_16;
}
}
lean_object* l_List_forM___at_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___at_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepBy1NoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 1, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 2);
x_20 = lean_ctor_get(x_10, 3);
x_21 = lean_ctor_get(x_10, 4);
x_22 = lean_ctor_get(x_10, 5);
x_23 = lean_ctor_get_uint8(x_10, sizeof(void*)*6);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_19);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set(x_25, 4, x_21);
lean_ctor_set(x_25, 5, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*6, x_23);
x_26 = lean_st_ref_set(x_3, x_25, x_11);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_27);
return x_28;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withoutPosition_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withForbidden_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withForbidden_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withForbidden_parenthesizer___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withForbidden_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_withForbidden_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withoutForbidden_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withoutInfo_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_incQuotDepth_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_decQuotDepth_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_suppressInsideQuot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_evalInsideQuot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_evalInsideQuot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_evalInsideQuot_parenthesizer___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_evalInsideQuot_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_evalInsideQuot_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedByCategoryToken_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedByCategoryToken_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_notFollowedByCategoryToken_parenthesizer___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedByCategoryToken_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_notFollowedByCategoryToken_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_3 == x_4;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
x_13 = l_Lean_interpolatedStrLitKind;
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = lean_apply_5(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = x_3 + x_18;
x_3 = x_19;
x_5 = x_16;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_25 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_7, x_8, x_9, x_10);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = 1;
x_29 = x_3 + x_28;
x_3 = x_29;
x_5 = x_26;
x_10 = x_27;
goto _start;
}
}
else
{
lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_10);
return x_31;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1___rarg___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_11 = l_Array_reverse___rarg(x_10);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_15 = l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___closed__1;
x_16 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_15, x_2, x_3, x_4, x_5, x_9);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_12, x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_18 = l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___closed__1;
x_19 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_18, x_2, x_3, x_4, x_5, x_9);
return x_19;
}
else
{
size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_21 = lean_box(0);
x_22 = l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___boxed__const__1;
x_23 = lean_box_usize(x_20);
x_24 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___spec__1___boxed), 10, 5);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_11);
lean_closure_set(x_24, 2, x_22);
lean_closure_set(x_24, 3, x_23);
lean_closure_set(x_24, 4, x_21);
x_25 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_24, x_2, x_3, x_4, x_5, x_9);
return x_25;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_dbgTraceState_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_dbgTraceState_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_dbgTraceState_parenthesizer___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_dbgTraceState_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_dbgTraceState_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_1 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_ite___rarg___boxed), 8, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_ite___rarg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_IO_mkRef___at_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3009____spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3009_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_IO_mkRef___at_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3009____spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_registerAlias(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
x_5 = l_Lean_Parser_registerAliasCore___rarg(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeParenthesizerParenthesizerAliasValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeArrowParenthesizerParenthesizerParenthesizerAliasValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeArrowParenthesizerArrowParenthesizerParenthesizerParenthesizerAliasValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("linebreak");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lookahead");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__15;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_atomic_parenthesizer), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__17;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__19;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__21;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__23;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__25;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__27;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
x_3 = l_term___x24_______closed__8;
x_4 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__2;
x_5 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Array_term_____x5b___x3a___x5d___closed__6;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__4;
x_9 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_7, x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__6;
x_12 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__8;
x_13 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_11, x_12, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Parser_Tactic_intro___closed__10;
x_16 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__10;
x_17 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_15, x_16, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Parser_Tactic_first___closed__8;
x_20 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__12;
x_21 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_19, x_20, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__14;
x_24 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__16;
x_25 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_23, x_24, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_term___x24_______closed__4;
x_28 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__18;
x_29 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_27, x_28, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_myMacro____x40_Init_Notation___hyg_1879____closed__4;
x_32 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__20;
x_33 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_31, x_32, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Parser_Tactic_first___closed__6;
x_36 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__22;
x_37 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_35, x_36, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_termS_x21_____closed__6;
x_40 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__24;
x_41 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_39, x_40, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_myMacro____x40_Init_Notation___hyg_1198____closed__6;
x_44 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__26;
x_45 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_43, x_44, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_Parser_Syntax_addPrec___closed__10;
x_48 = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__28;
x_49 = l_Lean_Parser_registerAliasCore___rarg(x_2, x_47, x_48, x_46);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
return x_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_45, 0);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_45);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_41);
if (x_54 == 0)
{
return x_41;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_41, 0);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_41);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_37);
if (x_58 == 0)
{
return x_37;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_37, 0);
x_60 = lean_ctor_get(x_37, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_37);
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
x_62 = !lean_is_exclusive(x_33);
if (x_62 == 0)
{
return x_33;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_33, 0);
x_64 = lean_ctor_get(x_33, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_33);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_29);
if (x_66 == 0)
{
return x_29;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_29, 0);
x_68 = lean_ctor_get(x_29, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_29);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_25);
if (x_70 == 0)
{
return x_25;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_25, 0);
x_72 = lean_ctor_get(x_25, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_25);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_21);
if (x_74 == 0)
{
return x_21;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_21, 0);
x_76 = lean_ctor_get(x_21, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_21);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_17);
if (x_78 == 0)
{
return x_17;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_17, 0);
x_80 = lean_ctor_get(x_17, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_17);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_13);
if (x_82 == 0)
{
return x_13;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_13, 0);
x_84 = lean_ctor_get(x_13, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_13);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_9);
if (x_86 == 0)
{
return x_9;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_9, 0);
x_88 = lean_ctor_get(x_9, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_9);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_5);
if (x_90 == 0)
{
return x_5;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_5, 0);
x_92 = lean_ctor_get(x_5, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_5);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_parenthesize_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_PrettyPrinter_parenthesize_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_parenthesize_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_parenthesize___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 3);
x_6 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_2, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_parenthesize___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_3, 3);
x_7 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_11, 3);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_1);
x_18 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_18, 0, x_1);
x_19 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__1;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__3;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
x_24 = l_Lean_KernelException_toMessageData___closed__15;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_6);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Std_PersistentArray_push___rarg(x_17, x_27);
lean_ctor_set(x_12, 0, x_28);
x_29 = lean_st_ref_set(x_4, x_11, x_13);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_36 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
x_37 = lean_ctor_get(x_12, 0);
lean_inc(x_37);
lean_dec(x_12);
lean_inc(x_1);
x_38 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_38, 0, x_1);
x_39 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__1;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__3;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_8);
x_44 = l_Lean_KernelException_toMessageData___closed__15;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
lean_inc(x_6);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_6);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Std_PersistentArray_push___rarg(x_37, x_47);
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_36);
lean_ctor_set(x_11, 3, x_49);
x_50 = lean_st_ref_set(x_4, x_11, x_13);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_55 = lean_ctor_get(x_11, 0);
x_56 = lean_ctor_get(x_11, 1);
x_57 = lean_ctor_get(x_11, 2);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_11);
x_58 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
x_59 = lean_ctor_get(x_12, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_60 = x_12;
} else {
 lean_dec_ref(x_12);
 x_60 = lean_box(0);
}
lean_inc(x_1);
x_61 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_61, 0, x_1);
x_62 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__1;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l___private_Lean_Util_Trace_0__Lean_addNode___rarg___lambda__1___closed__3;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_8);
x_67 = l_Lean_KernelException_toMessageData___closed__15;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_68);
lean_inc(x_6);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_6);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Std_PersistentArray_push___rarg(x_59, x_70);
if (lean_is_scalar(x_60)) {
 x_72 = lean_alloc_ctor(0, 1, 1);
} else {
 x_72 = x_60;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_58);
x_73 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_73, 0, x_55);
lean_ctor_set(x_73, 1, x_56);
lean_ctor_set(x_73, 2, x_57);
lean_ctor_set(x_73, 3, x_72);
x_74 = lean_st_ref_set(x_4, x_73, x_13);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
x_77 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_parenthesize___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Lean_checkTraceOption(x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesize: uncaught backtrack exception");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesize___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_parenthesize___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesize___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("input");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesize___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_2 = l_Lean_PrettyPrinter_parenthesize___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_parenthesize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_51; lean_object* x_52; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_st_ref_get(x_4, x_5);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 3);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_ctor_get_uint8(x_64, sizeof(void*)*1);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
lean_dec(x_62);
x_67 = 0;
x_51 = x_67;
x_52 = x_66;
goto block_61;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
lean_dec(x_62);
x_69 = l_Lean_PrettyPrinter_parenthesize___closed__4;
x_70 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_parenthesize___spec__3(x_69, x_3, x_4, x_68);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_unbox(x_71);
lean_dec(x_71);
x_51 = x_73;
x_52 = x_72;
goto block_61;
}
block_50:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = l_Lean_Syntax_Traverser_fromSyntax(x_2);
x_8 = lean_box(0);
x_9 = lean_box(0);
x_10 = 0;
x_11 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_8);
lean_ctor_set(x_11, 4, x_8);
lean_ctor_set(x_11, 5, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*6, x_10);
x_12 = lean_st_ref_get(x_4, x_6);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_mk_ref(x_11, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_15);
x_17 = lean_apply_5(x_1, x_9, x_15, x_3, x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_3);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_4, x_18);
lean_dec(x_4);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_15, x_20);
lean_dec(x_15);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_15);
x_30 = lean_ctor_get(x_17, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_17, 0);
lean_dec(x_32);
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_17);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_17, 1);
x_37 = lean_ctor_get(x_17, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
x_39 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_40 = lean_nat_dec_eq(x_39, x_38);
lean_dec(x_38);
if (x_40 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_free_object(x_17);
lean_dec(x_30);
x_41 = l_Lean_PrettyPrinter_parenthesize___closed__2;
x_42 = l_Lean_throwError___at_Lean_PrettyPrinter_parenthesize___spec__1(x_41, x_3, x_4, x_36);
lean_dec(x_4);
lean_dec(x_3);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_dec(x_17);
x_44 = lean_ctor_get(x_30, 0);
lean_inc(x_44);
x_45 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_46 = lean_nat_dec_eq(x_45, x_44);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_4);
lean_dec(x_3);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_30);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_30);
x_48 = l_Lean_PrettyPrinter_parenthesize___closed__2;
x_49 = l_Lean_throwError___at_Lean_PrettyPrinter_parenthesize___spec__1(x_48, x_3, x_4, x_43);
lean_dec(x_4);
lean_dec(x_3);
return x_49;
}
}
}
}
}
block_61:
{
if (x_51 == 0)
{
x_6 = x_52;
goto block_50;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_inc(x_2);
x_53 = l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_2);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_KernelException_toMessageData___closed__15;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_PrettyPrinter_parenthesize___closed__4;
x_59 = l_Lean_addTrace___at_Lean_PrettyPrinter_parenthesize___spec__2(x_58, x_57, x_3, x_4, x_52);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_6 = x_60;
goto block_50;
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_parenthesize___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_PrettyPrinter_parenthesize___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_parenthesize___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at_Lean_PrettyPrinter_parenthesize___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_parenthesize___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_parenthesize___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizeTerm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_term___u2218_____closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_parenthesizeTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_PrettyPrinter_parenthesizeTerm___closed__1;
x_6 = l_Lean_PrettyPrinter_parenthesize(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizeCommand___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_4320____closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_parenthesizeCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_PrettyPrinter_parenthesizeCommand___closed__1;
x_6 = l_Lean_PrettyPrinter_parenthesize(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3346_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_CoreM(lean_object*);
lean_object* initialize_Lean_KeyedDeclsAttribute(lean_object*);
lean_object* initialize_Lean_Parser_Extension(lean_object*);
lean_object* initialize_Lean_ParserCompiler_Attribute(lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_PrettyPrinter_Parenthesizer(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_KeyedDeclsAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Extension(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ParserCompiler_Attribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PrettyPrinter_Parenthesizer_Context_cat___default = _init_l_Lean_PrettyPrinter_Parenthesizer_Context_cat___default();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_Context_cat___default);
l_Lean_PrettyPrinter_Parenthesizer_State_contPrec___default = _init_l_Lean_PrettyPrinter_Parenthesizer_State_contPrec___default();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_State_contPrec___default);
l_Lean_PrettyPrinter_Parenthesizer_State_contCat___default = _init_l_Lean_PrettyPrinter_Parenthesizer_State_contCat___default();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_State_contCat___default);
l_Lean_PrettyPrinter_Parenthesizer_State_minPrec___default = _init_l_Lean_PrettyPrinter_Parenthesizer_State_minPrec___default();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_State_minPrec___default);
l_Lean_PrettyPrinter_Parenthesizer_State_trailPrec___default = _init_l_Lean_PrettyPrinter_Parenthesizer_State_trailPrec___default();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_State_trailPrec___default);
l_Lean_PrettyPrinter_Parenthesizer_State_trailCat___default = _init_l_Lean_PrettyPrinter_Parenthesizer_State_trailCat___default();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_State_trailCat___default);
l_Lean_PrettyPrinter_Parenthesizer_State_visitedToken___default = _init_l_Lean_PrettyPrinter_Parenthesizer_State_visitedToken___default();
l_Lean_PrettyPrinter_instOrElseParenthesizerM___closed__1 = _init_l_Lean_PrettyPrinter_instOrElseParenthesizerM___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_instOrElseParenthesizerM___closed__1);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__1 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__1);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__2 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__2);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__3 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__3);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__10 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__10);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__11 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__11);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__12 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__12);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__13 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__13();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__13);
res = l_Lean_PrettyPrinter_mkParenthesizerAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_parenthesizerAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute);
lean_dec_ref(res);
l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__1);
l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__2);
l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__1 = _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__1);
l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__2 = _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__2);
l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__3 = _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__3);
l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__4 = _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__4);
l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__5 = _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__5);
l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__6 = _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__6);
l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__7 = _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__7);
l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__8 = _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__8);
l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__9 = _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__9);
l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__10 = _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__10);
l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__11 = _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__11);
res = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_categoryParenthesizerAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_categoryParenthesizerAttribute);
lean_dec_ref(res);
l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__1 = _init_l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__1);
l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2 = _init_l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2);
l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__3 = _init_l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__3);
res = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_combinatorParenthesizerAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_combinatorParenthesizerAttribute);
lean_dec_ref(res);
l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__5 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__5);
l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM);
l_Lean_PrettyPrinter_Parenthesizer_visitArgs___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_visitArgs___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_visitArgs___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__5 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__5);
l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__6 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__6);
l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__7 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__7);
l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__8 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__8);
l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__9 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__9);
l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__10 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__10);
l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__11 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__11);
l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM);
l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7___closed__1 = _init_l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7___closed__1();
lean_mark_persistent(l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7___closed__1);
l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7___closed__2 = _init_l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7___closed__2();
lean_mark_persistent(l_Std_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__7 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__7);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__8 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__8);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__9 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__9);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__11 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__11);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__12 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__12);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__15 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__15();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__15);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__16 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__16();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__16);
l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1);
res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__5 = _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__5);
l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__6 = _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__6);
l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___boxed__const__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___boxed__const__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___boxed__const__1);
res = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3009_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef);
lean_dec_ref(res);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__1);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__2);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__3);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__4);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__5 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__5);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__6 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__6);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__7 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__7);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__8 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__8);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__9 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__9);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__10 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__10);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__11 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__11);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__12 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__12);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__13 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__13();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__13);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__14 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__14();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__14);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__15 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__15();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__15);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__16 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__16();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__16);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__17 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__17();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__17);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__18 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__18();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__18);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__19 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__19();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__19);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__20 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__20();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__20);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__21 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__21();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__21);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__22 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__22();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__22);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__23 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__23();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__23);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__24 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__24();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__24);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__25 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__25();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__25);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__26 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__26();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__26);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__27 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__27();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__27);
l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__28 = _init_l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__28();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076____closed__28);
res = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3076_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PrettyPrinter_parenthesize___closed__1 = _init_l_Lean_PrettyPrinter_parenthesize___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesize___closed__1);
l_Lean_PrettyPrinter_parenthesize___closed__2 = _init_l_Lean_PrettyPrinter_parenthesize___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesize___closed__2);
l_Lean_PrettyPrinter_parenthesize___closed__3 = _init_l_Lean_PrettyPrinter_parenthesize___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesize___closed__3);
l_Lean_PrettyPrinter_parenthesize___closed__4 = _init_l_Lean_PrettyPrinter_parenthesize___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesize___closed__4);
l_Lean_PrettyPrinter_parenthesizeTerm___closed__1 = _init_l_Lean_PrettyPrinter_parenthesizeTerm___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizeTerm___closed__1);
l_Lean_PrettyPrinter_parenthesizeCommand___closed__1 = _init_l_Lean_PrettyPrinter_parenthesizeCommand___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizeCommand___closed__1);
res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3346_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
