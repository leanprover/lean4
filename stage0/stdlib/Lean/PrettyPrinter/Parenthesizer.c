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
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withoutInfo_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer(lean_object*);
uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object*);
static lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__3;
size_t l_USize_add(size_t, size_t);
static lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__1;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___rarg(lean_object*);
uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_categoryParenthesizerAttribute;
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_optionalNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer(lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesize___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_parenthesize___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__1;
extern lean_object* l_Lean_nullKind;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer(lean_object*, uint8_t, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__19;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__11;
static lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_evalInsideQuot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__11;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_up(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__8;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__7;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__10;
static lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__10;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesize___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesizeCommand___closed__3;
static lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_parenthesize___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__7;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_Context_cat___default;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_addTrace_addTraceOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___boxed(lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3449_(lean_object*);
static lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeArrowParenthesizerParenthesizerParenthesizerAliasValue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_evalInsideQuot_parenthesizer___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withoutPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Level_PP_Result_quote___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__13;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_State_trailCat___default;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__2;
lean_object* l_List_range(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizeCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_State_trailPrec___default;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__8;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizeTerm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedByCategoryToken_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_instOrElseParenthesizerM(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___rarg(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__1;
lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_runForNodeKind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__5;
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__12;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__9;
lean_object* l_Array_back_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__11;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_atomic_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__11;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_dbgTraceState_parenthesizer___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_registerAlias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_parenthesize___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__5;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2(lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesizeTactic___closed__1;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1;
static lean_object* l_Lean_PrettyPrinter_parenthesize___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerAliasCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_pretty_printer_parenthesizer_interpret_parser_descr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__3;
static lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLiftReaderT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__2(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_many1NoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__5;
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__7___closed__1;
lean_object* l_Lean_Syntax_Traverser_setCur(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__1;
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__3;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_dbgTraceState_parenthesizer(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__13;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__1;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__6;
static lean_object* l_Lean_PrettyPrinter_parenthesizeCommand___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__7___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__1;
static lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2;
lean_object* l_StateRefT_x27_lift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__6;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesize___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadRefCoreM;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_suppressInsideQuot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__6;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ParenthesizerM_orElse(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__6;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__1;
static lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withForbidden_parenthesizer(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Unhygienic_run___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedByCategoryToken_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__12;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_incQuotDepth_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParserOfStack_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctorReaderT___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_parenthesize___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__7;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__16;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withoutForbidden_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_parenthesize___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__13;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__4___boxed(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM(lean_object*);
extern lean_object* l_Lean_Parser_maxPrec;
static lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__11;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepBy1NoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1___closed__1;
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getValues___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___rarg(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__11;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__4;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__4(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__9;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_State_contPrec___default;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__13;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_many1Unbox_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withOpenDecl_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__10;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__8;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer___rarg(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Parenthesizer_State_visitedToken___default;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__3;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__3;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__5;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___rarg(lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__14;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__1;
static lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__9;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonadEStateM(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__2;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg___closed__1;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__14;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_evalInsideQuot_parenthesizer(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___rarg(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute(lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__5;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__2;
lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__5;
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__15;
static lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__15;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__18;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__8___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__4;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ParenthesizerM_orElse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__6;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_decQuotDepth_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_down(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeArrowParenthesizerArrowParenthesizerParenthesizerParenthesizerAliasValue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3227_(lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__16;
static lean_object* l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer(lean_object*);
uint8_t l_Lean_Parser_isParserCategory(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__2(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedByCategoryToken_parenthesizer___rarg(lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__10;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_dbgTraceState_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__6;
static lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_right(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_mkParenthesizerAttribute___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1(lean_object*);
static lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withForbidden_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__12;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___rarg(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__2;
static lean_object* l_Lean_PrettyPrinter_parenthesizeCommand___closed__1;
static lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__1;
LEAN_EXPORT lean_object* l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(lean_object*);
static lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizeTactic(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__1;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__10;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__20;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__12;
static lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__14;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__2;
static lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint32_t l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___closed__2;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__6___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__15;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeParenthesizerParenthesizerAliasValue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_mkParenthesizerAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_State_contCat___default;
static lean_object* l_Lean_PrettyPrinter_instOrElseParenthesizerM___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_parenthesize___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withOpen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__6;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
LEAN_EXPORT lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3;
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withForbidden_parenthesizer___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_State_minPrec___default;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__14;
static lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__3;
lean_object* l_IO_mkRef___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__5;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__7;
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___boxed__const__1;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___closed__1;
lean_object* l_Nat_min(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__6;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_backtrackExceptionId;
static lean_object* l_Lean_PrettyPrinter_parenthesizeTerm___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__3;
static lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__4;
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__17;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParserOfStack_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__8;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__1;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesize___closed__2;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__9;
extern lean_object* l_Lean_interpolatedStrLitKind;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__10;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadRef___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___closed__1;
static lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__4;
static lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__9;
lean_object* lean_mk_antiquot_parenthesizer(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getId(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ParenthesizerM_orElse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
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
x_29 = lean_box(0);
x_30 = lean_apply_6(x_2, x_29, x_3, x_4, x_5, x_6, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_dec(x_13);
x_32 = lean_ctor_get(x_14, 0);
lean_inc(x_32);
x_33 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_34 = lean_nat_dec_eq(x_33, x_32);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_14);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_14);
x_36 = lean_st_ref_get(x_6, x_31);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_st_ref_set(x_4, x_11, x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = lean_apply_6(x_2, x_40, x_3, x_4, x_5, x_6, x_39);
return x_41;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ParenthesizerM_orElse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ParenthesizerM_orElse___rarg), 7, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_instOrElseParenthesizerM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ParenthesizerM_orElse___rarg), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_instOrElseParenthesizerM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_instOrElseParenthesizerM___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_mkParenthesizerAttribute___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_inc(x_4);
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
lean_dec(x_4);
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
lean_inc(x_12);
x_16 = l_Lean_Parser_isValidSyntaxNodeKind(x_10, x_12);
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
x_20 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at_Lean_PrettyPrinter_mkParenthesizerAttribute___spec__1(x_21, x_3, x_4, x_13);
lean_dec(x_4);
lean_dec(x_3);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_4);
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
lean_dec(x_4);
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
lean_inc(x_4);
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
lean_dec(x_4);
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
lean_inc(x_36);
x_40 = l_Lean_Parser_isValidSyntaxNodeKind(x_34, x_36);
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
x_44 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__4;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_throwError___at_Lean_PrettyPrinter_mkParenthesizerAttribute___spec__1(x_45, x_3, x_4, x_37);
lean_dec(x_4);
lean_dec(x_3);
return x_46;
}
else
{
lean_object* x_47; 
lean_dec(x_4);
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
lean_dec(x_4);
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
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PrettyPrinter");
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
x_1 = lean_mk_string("Parenthesizer");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Register a parenthesizer for a parser.\n\n  [parenthesizer k] registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` for the `SyntaxNodeKind` `k`.");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__2;
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
x_3 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__11;
x_4 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__10;
x_5 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__12;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesizerAttribute");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__13;
x_3 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__15;
x_4 = l_Lean_KeyedDeclsAttribute_init___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_mkParenthesizerAttribute___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_PrettyPrinter_mkParenthesizerAttribute___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1___closed__2;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
static uint32_t _init_l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__3() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__1;
x_3 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__2;
x_4 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__3;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__4___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__3;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__7___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__2;
x_3 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__1;
x_4 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
lean_ctor_set(x_4, 4, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__3___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__4___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__5___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__3;
x_3 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__4;
x_4 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__5;
x_5 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__6;
x_6 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__7;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__6___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__7___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__8___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__10;
x_2 = lean_box(0);
x_3 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__11;
x_4 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__6;
x_5 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__12;
x_6 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__13;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__8;
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__14;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__2;
x_2 = lean_box(0);
x_3 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__15;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__4(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__6(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__7___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__7(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__8___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__8(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [categoryParenthesizer] argument, unknown parser category '");
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_inc(x_4);
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
lean_inc(x_12);
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
x_20 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at_Lean_PrettyPrinter_mkParenthesizerAttribute___spec__1(x_21, x_3, x_4, x_13);
lean_dec(x_4);
lean_dec(x_3);
return x_22;
}
else
{
lean_dec(x_4);
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
lean_inc(x_23);
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
x_31 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__4;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_PrettyPrinter_mkParenthesizerAttribute___spec__1(x_32, x_3, x_4, x_24);
lean_dec(x_4);
lean_dec(x_3);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_4);
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
lean_dec(x_4);
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
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
x_2 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Register a parenthesizer for a syntax category.\n\n  [categoryParenthesizer cat] registers a declaration of type `Lean.PrettyPrinter.CategoryParenthesizer` for the category `cat`,\n  which is used when parenthesizing calls of `categoryParser cat prec`. Implementations should call `maybeParenthesize`\n  with the precedence and `cat`. If no category parenthesizer is registered, the category will never be parenthesized,\n  but still be traversed for parenthesizing nested categories.");
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
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
x_2 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__9;
x_3 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__11;
x_4 = l_Lean_KeyedDeclsAttribute_init___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1(x_6, x_2, x_3, x_4, x_5);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
x_3 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__3;
x_4 = l_Lean_ParserCompiler_registerCombinatorAttribute(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1___closed__2;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1___closed__2;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__2;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__1;
x_2 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__2;
x_3 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__4;
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__14;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___lambda__1(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg), 1, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___spec__1___rarg), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_st_ref_get(x_2, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__2___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__1;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___spec__1___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__3___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__4___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__3;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__4;
x_3 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__5;
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
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__6;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_3, x_4, x_5, x_6);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_1; 
x_1 = l_EStateM_instMonadEStateM(lean_box(0), lean_box(0));
return x_1;
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
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__4;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__5;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadFunctorReaderT___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_lift), 4, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__4;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadFunctorReaderT___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__7;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__8;
x_3 = l_Lean_Core_instMonadRefCoreM;
x_4 = l_Lean_instMonadRef___rarg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__1;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__6;
x_3 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__9;
x_4 = l_Lean_instMonadRef___rarg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1___rarg___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1___rarg___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___lambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__10;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__11;
x_3 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__12;
x_4 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__13;
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
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__14;
return x_1;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_traceMsg");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] ");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_addTrace_addTraceOptions(x_10);
x_13 = lean_st_ref_take(x_6, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_14, 3);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__2;
x_22 = l_Lean_Name_append(x_1, x_21);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_1);
x_24 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__6;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_12);
x_29 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__7;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
lean_inc(x_8);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Std_PersistentArray_push___rarg(x_20, x_32);
lean_ctor_set(x_15, 0, x_33);
x_34 = lean_st_ref_set(x_6, x_14, x_16);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_41 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
x_42 = lean_ctor_get(x_15, 0);
lean_inc(x_42);
lean_dec(x_15);
x_43 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__2;
x_44 = l_Lean_Name_append(x_1, x_43);
x_45 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_45, 0, x_1);
x_46 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__4;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__6;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_12);
x_51 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__7;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_52);
lean_inc(x_8);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_8);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Std_PersistentArray_push___rarg(x_42, x_54);
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_41);
lean_ctor_set(x_14, 3, x_56);
x_57 = lean_st_ref_set(x_6, x_14, x_16);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_62 = lean_ctor_get(x_14, 0);
x_63 = lean_ctor_get(x_14, 1);
x_64 = lean_ctor_get(x_14, 2);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_14);
x_65 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
x_66 = lean_ctor_get(x_15, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_67 = x_15;
} else {
 lean_dec_ref(x_15);
 x_67 = lean_box(0);
}
x_68 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__2;
x_69 = l_Lean_Name_append(x_1, x_68);
x_70 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_70, 0, x_1);
x_71 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__4;
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__6;
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_12);
x_76 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__7;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_78, 0, x_69);
lean_ctor_set(x_78, 1, x_77);
lean_inc(x_8);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_8);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Std_PersistentArray_push___rarg(x_66, x_79);
if (lean_is_scalar(x_67)) {
 x_81 = lean_alloc_ctor(0, 1, 1);
} else {
 x_81 = x_67;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_65);
x_82 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_82, 0, x_62);
lean_ctor_set(x_82, 1, x_63);
lean_ctor_set(x_82, 2, x_64);
lean_ctor_set(x_82, 3, x_81);
x_83 = lean_st_ref_set(x_6, x_82, x_16);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___rarg___boxed), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("none");
return x_1;
}
}
static lean_object* _init_l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("some ");
return x_1;
}
}
static lean_object* _init_l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__2;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Nat_repr(x_3);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__4;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_1, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_7, x_8, x_9, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_9, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_take(x_7, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_18, 4);
lean_dec(x_21);
x_22 = lean_ctor_get(x_18, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_18, 1);
lean_dec(x_23);
x_24 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1;
lean_ctor_set(x_18, 4, x_3);
lean_ctor_set(x_18, 2, x_2);
lean_ctor_set(x_18, 1, x_24);
x_25 = lean_st_ref_set(x_7, x_18, x_19);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = lean_apply_6(x_4, x_27, x_6, x_7, x_8, x_9, x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 3);
x_31 = lean_ctor_get(x_18, 5);
x_32 = lean_ctor_get_uint8(x_18, sizeof(void*)*6);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1;
x_34 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_2);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_3);
lean_ctor_set(x_34, 5, x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*6, x_32);
x_35 = lean_st_ref_set(x_7, x_34, x_19);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_box(0);
x_38 = lean_apply_6(x_4, x_37, x_6, x_7, x_8, x_9, x_36);
return x_38;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesized: ");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_6);
x_29 = lean_st_ref_get(x_10, x_11);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*1);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = 0;
x_12 = x_34;
x_13 = x_33;
goto block_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
lean_inc(x_4);
x_36 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_4, x_7, x_8, x_9, x_10, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_unbox(x_37);
lean_dec(x_37);
x_12 = x_39;
x_13 = x_38;
goto block_28;
}
block_28:
{
if (x_12 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3(x_5, x_1, x_2, x_3, x_14, x_7, x_8, x_9, x_10, x_13);
return x_15;
}
else
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = 0;
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_18 = l_Lean_Syntax_formatStxAux(x_2, x_16, x_17, x_5);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__7;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_4, x_23, x_7, x_8, x_9, x_10, x_13);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3(x_5, x_1, x_2, x_3, x_25, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_25);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__2;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_dec(x_7);
x_13 = l_Lean_Syntax_getTailInfo(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___closed__2;
lean_ctor_set(x_13, 0, x_16);
x_17 = l_Lean_Syntax_setTailInfo(x_6, x_13);
x_18 = lean_box(0);
x_19 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4(x_1, x_2, x_3, x_4, x_17, x_18, x_8, x_9, x_10, x_11, x_12);
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
x_23 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___closed__2;
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
x_25 = l_Lean_Syntax_setTailInfo(x_6, x_24);
x_26 = lean_box(0);
x_27 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4(x_1, x_2, x_3, x_4, x_25, x_26, x_8, x_9, x_10, x_11, x_12);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_13);
x_28 = lean_box(0);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4(x_1, x_2, x_3, x_4, x_6, x_28, x_8, x_9, x_10, x_11, x_12);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
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
x_17 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___closed__2;
lean_ctor_set(x_14, 2, x_17);
x_18 = l_Lean_Syntax_setHeadInfo(x_13, x_14);
x_19 = lean_box(0);
x_20 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5(x_2, x_3, x_4, x_5, x_6, x_18, x_19, x_8, x_9, x_10, x_11, x_12);
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
x_24 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___closed__2;
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_23);
x_26 = l_Lean_Syntax_setHeadInfo(x_13, x_25);
x_27 = lean_box(0);
x_28 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5(x_2, x_3, x_4, x_5, x_6, x_26, x_27, x_8, x_9, x_10, x_11, x_12);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_14);
x_29 = lean_box(0);
x_30 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5(x_2, x_3, x_4, x_5, x_6, x_13, x_29, x_8, x_9, x_10, x_11, x_12);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_dec(x_7);
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
x_16 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___closed__2;
lean_ctor_set(x_13, 2, x_16);
x_17 = l_Lean_Syntax_setTailInfo(x_6, x_13);
x_18 = lean_box(0);
x_19 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__6(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12);
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
x_23 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___closed__2;
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_22);
x_25 = l_Lean_Syntax_setTailInfo(x_6, x_24);
x_26 = lean_box(0);
x_27 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__6(x_1, x_2, x_3, x_4, x_5, x_25, x_26, x_8, x_9, x_10, x_11, x_12);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_13);
x_28 = lean_box(0);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_28, x_8, x_9, x_10, x_11, x_12);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
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
x_18 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___closed__2;
lean_ctor_set(x_15, 0, x_18);
x_19 = l_Lean_Syntax_setHeadInfo(x_13, x_15);
x_20 = lean_box(0);
x_21 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__7(x_1, x_2, x_3, x_4, x_5, x_19, x_20, x_7, x_8, x_9, x_10, x_14);
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
x_25 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___closed__2;
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_24);
x_27 = l_Lean_Syntax_setHeadInfo(x_13, x_26);
x_28 = lean_box(0);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__7(x_1, x_2, x_3, x_4, x_5, x_27, x_28, x_7, x_8, x_9, x_10, x_14);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_15);
x_30 = lean_box(0);
x_31 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__7(x_1, x_2, x_3, x_4, x_5, x_13, x_30, x_7, x_8, x_9, x_10, x_14);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__9(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_35; 
x_23 = lean_box(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___boxed), 12, 6);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_23);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_4);
lean_closure_set(x_24, 4, x_5);
lean_closure_set(x_24, 5, x_6);
x_35 = lean_nat_dec_lt(x_11, x_3);
lean_dec(x_11);
if (x_35 == 0)
{
if (x_12 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_36 = lean_box(0);
x_37 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_36, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
return x_37;
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_38 = lean_box(0);
x_39 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_38, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
return x_39;
}
else
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_40 = lean_box(0);
x_41 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_40, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_13, 0);
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_name_eq(x_15, x_16);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_45 = lean_box(0);
x_46 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_45, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
return x_46;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_42, x_43);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_48 = lean_box(0);
x_49 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_48, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_50 = lean_box(0);
x_25 = x_50;
goto block_34;
}
}
}
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_51 = lean_box(0);
x_25 = x_51;
goto block_34;
}
block_34:
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_25);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_lt(x_26, x_10);
lean_dec(x_10);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__8(x_7, x_4, x_8, x_24, x_9, x_28, x_18, x_19, x_20, x_21, x_22);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___rarg(x_19, x_20, x_21, x_22);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__8(x_7, x_4, x_8, x_24, x_9, x_31, x_18, x_19, x_20, x_21, x_32);
return x_33;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("visited a syntax tree without precedences?!");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("...precedences are ");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" >? ");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", ");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(",");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__11;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__13;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__14;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__17;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" <=? ");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__19;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, uint8_t x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; 
lean_dec(x_16);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_22 = lean_apply_5(x_1, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_st_ref_get(x_20, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_get(x_18, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_30 = x_26;
} else {
 lean_dec_ref(x_26);
 x_30 = lean_box(0);
}
x_47 = lean_st_ref_get(x_20, x_29);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 3);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get_uint8(x_49, sizeof(void*)*1);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = 0;
x_31 = x_52;
x_32 = x_51;
goto block_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_dec(x_47);
lean_inc(x_4);
x_54 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_4, x_17, x_18, x_19, x_20, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_unbox(x_55);
lean_dec(x_55);
x_31 = x_57;
x_32 = x_56;
goto block_46;
}
block_46:
{
if (x_31 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_box(0);
if (lean_is_scalar(x_30)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_30;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_30);
x_35 = 0;
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_Syntax_formatStxAux(x_2, x_35, x_36, x_3);
lean_dec(x_2);
x_38 = lean_box(1);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__2;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__7;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_4, x_44, x_17, x_18, x_19, x_20, x_32);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
return x_45;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
lean_dec(x_3);
x_58 = lean_ctor_get(x_26, 1);
lean_inc(x_58);
lean_dec(x_26);
x_59 = lean_ctor_get(x_27, 4);
lean_inc(x_59);
x_60 = lean_ctor_get(x_27, 5);
lean_inc(x_60);
lean_dec(x_27);
x_61 = lean_ctor_get(x_28, 0);
lean_inc(x_61);
lean_dec(x_28);
x_126 = lean_st_ref_get(x_20, x_58);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 3);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_ctor_get_uint8(x_128, sizeof(void*)*1);
lean_dec(x_128);
if (x_129 == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_126, 1);
lean_inc(x_130);
lean_dec(x_126);
x_131 = 0;
x_62 = x_131;
x_63 = x_130;
goto block_125;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_132 = lean_ctor_get(x_126, 1);
lean_inc(x_132);
lean_dec(x_126);
lean_inc(x_4);
x_133 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_4, x_17, x_18, x_19, x_20, x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_unbox(x_134);
lean_dec(x_134);
x_62 = x_136;
x_63 = x_135;
goto block_125;
}
block_125:
{
if (x_62 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_box(0);
x_65 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__9(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_2, x_4, x_12, x_61, x_13, x_59, x_14, x_60, x_15, x_64, x_17, x_18, x_19, x_20, x_63);
lean_dec(x_15);
lean_dec(x_60);
lean_dec(x_14);
lean_dec(x_59);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_inc(x_7);
x_66 = l_Nat_repr(x_7);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__4;
x_70 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__6;
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
lean_inc(x_61);
x_73 = l_Nat_repr(x_61);
x_74 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__7;
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
if (x_13 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__8;
x_80 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
lean_inc(x_4);
x_81 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_4, x_80, x_17, x_18, x_19, x_20, x_63);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__9(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_2, x_4, x_12, x_61, x_13, x_59, x_14, x_60, x_15, x_82, x_17, x_18, x_19, x_20, x_83);
lean_dec(x_82);
lean_dec(x_15);
lean_dec(x_60);
lean_dec(x_14);
lean_dec(x_59);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_inc(x_59);
x_85 = l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_59);
x_86 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__12;
x_87 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_box(1);
x_89 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = 1;
lean_inc(x_60);
x_91 = l_Lean_Name_toString(x_60, x_90);
x_92 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__16;
x_95 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__18;
x_97 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__15;
x_99 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = 0;
x_101 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*1, x_100);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__10;
x_104 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__20;
x_106 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
lean_inc(x_14);
x_107 = l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_14);
x_108 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_86);
x_109 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_88);
lean_inc(x_15);
x_110 = l_Lean_Name_toString(x_15, x_90);
x_111 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_113, 0, x_94);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_96);
x_115 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_115, 0, x_98);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_100);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_118, 0, x_106);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_77);
x_120 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_120, 0, x_78);
lean_ctor_set(x_120, 1, x_119);
lean_inc(x_4);
x_121 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_4, x_120, x_17, x_18, x_19, x_20, x_63);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__9(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_2, x_4, x_12, x_61, x_13, x_59, x_14, x_60, x_15, x_122, x_17, x_18, x_19, x_20, x_123);
lean_dec(x_122);
lean_dec(x_15);
lean_dec(x_60);
lean_dec(x_14);
lean_dec(x_59);
return x_124;
}
}
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = !lean_is_exclusive(x_22);
if (x_137 == 0)
{
return x_22;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_22, 0);
x_139 = lean_ctor_get(x_22, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_22);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
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
x_1 = lean_mk_string("parenthesizing (cont := ");
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__17;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
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
x_36 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_75 = lean_st_ref_get(x_9, x_35);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_76, 3);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_ctor_get_uint8(x_77, sizeof(void*)*1);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
x_37 = x_31;
x_38 = x_79;
goto block_74;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
lean_dec(x_75);
x_81 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_36, x_6, x_7, x_8, x_9, x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_unbox(x_82);
lean_dec(x_82);
x_37 = x_84;
x_38 = x_83;
goto block_74;
}
block_74:
{
if (x_37 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_box(0);
x_40 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10(x_5, x_29, x_12, x_36, x_25, x_28, x_4, x_1, x_26, x_27, x_3, x_15, x_2, x_23, x_24, x_39, x_6, x_7, x_8, x_9, x_38);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_inc(x_23);
x_41 = l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_23);
x_42 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__12;
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_box(1);
x_45 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = 1;
lean_inc(x_24);
x_47 = l_Lean_Name_toString(x_24, x_46);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__16;
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__18;
x_53 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__15;
x_55 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = 0;
x_57 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6;
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
x_64 = l_Lean_Syntax_formatStxAux(x_29, x_31, x_63, x_12);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = l_Lean_indentD(x_65);
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__7;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_36, x_69, x_6, x_7, x_8, x_9, x_38);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10(x_5, x_29, x_12, x_36, x_25, x_28, x_4, x_1, x_26, x_27, x_3, x_15, x_2, x_23, x_24, x_71, x_6, x_7, x_8, x_9, x_72);
return x_73;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_85 = lean_ctor_get(x_20, 0);
x_86 = lean_ctor_get(x_20, 1);
x_87 = lean_ctor_get(x_20, 2);
x_88 = lean_ctor_get(x_20, 3);
x_89 = lean_ctor_get(x_20, 4);
x_90 = lean_ctor_get(x_20, 5);
x_91 = lean_ctor_get_uint8(x_20, sizeof(void*)*6);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_20);
x_92 = lean_box(0);
x_93 = lean_box(0);
x_94 = 0;
x_95 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_95, 0, x_85);
lean_ctor_set(x_95, 1, x_92);
lean_ctor_set(x_95, 2, x_93);
lean_ctor_set(x_95, 3, x_92);
lean_ctor_set(x_95, 4, x_92);
lean_ctor_set(x_95, 5, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*6, x_94);
x_96 = lean_st_ref_get(x_9, x_21);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_st_ref_set(x_7, x_95, x_97);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_139 = lean_st_ref_get(x_9, x_99);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_140, 3);
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_ctor_get_uint8(x_141, sizeof(void*)*1);
lean_dec(x_141);
if (x_142 == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
lean_dec(x_139);
x_101 = x_94;
x_102 = x_143;
goto block_138;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_144 = lean_ctor_get(x_139, 1);
lean_inc(x_144);
lean_dec(x_139);
x_145 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_100, x_6, x_7, x_8, x_9, x_144);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_unbox(x_146);
lean_dec(x_146);
x_101 = x_148;
x_102 = x_147;
goto block_138;
}
block_138:
{
if (x_101 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_box(0);
x_104 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10(x_5, x_92, x_12, x_100, x_88, x_91, x_4, x_1, x_89, x_90, x_3, x_15, x_2, x_86, x_87, x_103, x_6, x_7, x_8, x_9, x_102);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_inc(x_86);
x_105 = l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_86);
x_106 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__12;
x_107 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_box(1);
x_109 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = 1;
lean_inc(x_87);
x_111 = l_Lean_Name_toString(x_87, x_110);
x_112 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_113, 0, x_109);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__16;
x_115 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__18;
x_117 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__15;
x_119 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
x_120 = 0;
x_121 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set_uint8(x_121, sizeof(void*)*1, x_120);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_124 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
x_125 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6;
x_126 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
x_128 = l_Lean_Syntax_formatStxAux(x_92, x_94, x_127, x_12);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = l_Lean_indentD(x_129);
x_131 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_131, 0, x_126);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__7;
x_133 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_100, x_133, x_6, x_7, x_8, x_9, x_102);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10(x_5, x_92, x_12, x_100, x_88, x_91, x_4, x_1, x_89, x_90, x_3, x_15, x_2, x_86, x_87, x_135, x_6, x_7, x_8, x_9, x_136);
return x_137;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__9___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
_start:
{
uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_unbox(x_2);
lean_dec(x_2);
x_24 = lean_unbox(x_12);
lean_dec(x_12);
x_25 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__9(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_unbox(x_6);
lean_dec(x_6);
x_23 = lean_unbox(x_13);
lean_dec(x_13);
x_24 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10(x_1, x_2, x_3, x_4, x_5, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_23, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_visitToken(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_mk_antiquot_parenthesizer(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_3(x_1, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_liftCoreM___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_liftCoreM___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_1 = lean_mk_string("missing");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr_x27___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__2;
x_8 = lean_name_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_10 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___rarg), 1, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquotSuffixSplice_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_tokenWithAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("choice");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = l_Lean_Syntax_getKind(x_9);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___closed__2;
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
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_inc(x_1);
x_13 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_12, x_11, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParserOfStack_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParserOfStack_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_categoryParserOfStack_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_parserOfStack_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Term");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("paren");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("null");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__8;
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__7___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__13;
lean_inc(x_2);
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__10;
x_8 = lean_array_push(x_7, x_1);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__9;
x_10 = lean_array_push(x_8, x_9);
x_11 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__8;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__17;
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__11;
x_16 = lean_array_push(x_15, x_6);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_14);
x_19 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Level_PP_Result_quote___spec__1), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__2___closed__1;
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
x_1 = lean_mk_string("term");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__2), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_13 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2;
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore), 7, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_1);
x_15 = 1;
x_16 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__10;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1;
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_categoryParenthesizerAttribute;
x_3 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2;
x_5 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__2;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tacticSeq");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__2;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__13;
lean_inc(x_2);
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__6;
x_8 = lean_array_push(x_7, x_1);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__5;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__17;
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__11;
x_14 = lean_array_push(x_13, x_6);
x_15 = lean_array_push(x_14, x_10);
x_16 = lean_array_push(x_15, x_12);
x_17 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__3;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__2___closed__1;
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
x_1 = lean_mk_string("tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__2), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = 0;
x_10 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3;
x_11 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_7, x_9, x_10, x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__10;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1;
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_categoryParenthesizerAttribute;
x_3 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2;
x_5 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Level");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__2;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__13;
lean_inc(x_2);
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__17;
x_8 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__11;
x_10 = lean_array_push(x_9, x_6);
x_11 = lean_array_push(x_10, x_1);
x_12 = lean_array_push(x_11, x_8);
x_13 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__3;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__2___closed__1;
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
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__2), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = 0;
x_10 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3;
x_11 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_7, x_9, x_10, x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__10;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1;
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_categoryParenthesizerAttribute;
x_3 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2;
x_5 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer___rarg), 1, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___rarg), 1, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_atomic_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___rarg), 1, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___rarg), 1, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg(x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__1___boxed), 7, 1);
lean_closure_set(x_11, 0, x_2);
x_12 = l_Lean_Syntax_getKind(x_9);
x_13 = lean_name_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_2);
x_14 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_33 = lean_st_ref_get(x_6, x_10);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 3);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = 0;
x_15 = x_38;
x_16 = x_37;
goto block_32;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_14, x_3, x_4, x_5, x_6, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_unbox(x_41);
lean_dec(x_41);
x_15 = x_43;
x_16 = x_42;
goto block_32;
}
block_32:
{
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__2(x_11, x_17, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_11);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_19, 0, x_12);
x_20 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__6;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__4;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_14, x_27, x_3, x_4, x_5, x_6, x_16);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__2(x_11, x_29, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_29);
lean_dec(x_11);
return x_31;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_44 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_2, x_3, x_4, x_5, x_6, x_10);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1___rarg), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_7, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_14, 2);
lean_dec(x_17);
lean_inc(x_4);
lean_ctor_set(x_14, 2, x_4);
x_18 = lean_st_ref_set(x_5, x_14, x_15);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_4);
x_20 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_4, x_2, x_4, x_5, x_6, x_7, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
x_23 = lean_ctor_get(x_14, 3);
x_24 = lean_ctor_get(x_14, 4);
x_25 = lean_ctor_get(x_14, 5);
x_26 = lean_ctor_get_uint8(x_14, sizeof(void*)*6);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
lean_inc(x_4);
x_27 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_4);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set(x_27, 5, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*6, x_26);
x_28 = lean_st_ref_set(x_5, x_27, x_15);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_4);
x_30 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_4, x_2, x_4, x_5, x_6, x_7, x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___boxed), 8, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1___rarg), 7, 2);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__2___boxed), 9, 3);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_4);
x_14 = l_Lean_Syntax_getKind(x_11);
x_15 = lean_name_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_35 = lean_st_ref_get(x_8, x_12);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 3);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = 0;
x_17 = x_40;
x_18 = x_39;
goto block_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_dec(x_35);
x_42 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_16, x_5, x_6, x_7, x_8, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_unbox(x_43);
lean_dec(x_43);
x_17 = x_45;
x_18 = x_44;
goto block_34;
}
block_34:
{
if (x_17 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__2(x_13, x_19, x_5, x_6, x_7, x_8, x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_13);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_14);
x_22 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__4;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__6;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_26, 0, x_1);
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__4;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_16, x_29, x_5, x_6, x_7, x_8, x_18);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__2(x_13, x_31, x_5, x_6, x_7, x_8, x_32);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_31);
lean_dec(x_13);
return x_33;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_46 = lean_box(0);
x_47 = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__2(x_2, x_3, x_4, x_46, x_5, x_6, x_7, x_8, x_12);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Lean_PrettyPrinter_Parenthesizer_rawCh_parenthesizer(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_symbolNoAntiquot_parenthesizer(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbolNoAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_rawIdentNoAntiquot_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbolNoAntiquot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_scientificLitNoAntiquot_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_forM_loop___at_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_many1NoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_manyNoAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_many1Unbox_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_optionalNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_List_forM___at_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___at_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepBy1NoAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withoutPosition_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withForbidden_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withForbidden_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withForbidden_parenthesizer___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withForbidden_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_withForbidden_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withoutForbidden_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withoutInfo_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_incQuotDepth_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_decQuotDepth_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_suppressInsideQuot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_evalInsideQuot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_evalInsideQuot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_evalInsideQuot_parenthesizer___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_evalInsideQuot_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_evalInsideQuot_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedByCategoryToken_parenthesizer___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedByCategoryToken_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_notFollowedByCategoryToken_parenthesizer___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedByCategoryToken_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withOpenDecl_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_withOpen_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_dbgTraceState_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_dbgTraceState_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_dbgTraceState_parenthesizer___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_dbgTraceState_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_dbgTraceState_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_ite___rarg___boxed), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_ite___rarg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3227_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_IO_mkRef___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_registerAlias(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
x_5 = l_Lean_Parser_registerAliasCore___rarg(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeParenthesizerParenthesizerAliasValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeArrowParenthesizerParenthesizerParenthesizerAliasValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Parenthesizer_instCoeArrowParenthesizerArrowParenthesizerParenthesizerParenthesizerAliasValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_parenthesize___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_parenthesize___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_ctor_get(x_3, 3);
x_7 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_addTrace_addTraceOptions(x_8);
x_11 = lean_st_ref_take(x_4, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_12, 3);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__2;
x_20 = l_Lean_Name_append(x_1, x_19);
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__4;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__6;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_10);
x_27 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__7;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_6);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_6);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Std_PersistentArray_push___rarg(x_18, x_30);
lean_ctor_set(x_13, 0, x_31);
x_32 = lean_st_ref_set(x_4, x_12, x_14);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_39 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
x_40 = lean_ctor_get(x_13, 0);
lean_inc(x_40);
lean_dec(x_13);
x_41 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__2;
x_42 = l_Lean_Name_append(x_1, x_41);
x_43 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_43, 0, x_1);
x_44 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__4;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__6;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_10);
x_49 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__7;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_6);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_6);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Std_PersistentArray_push___rarg(x_40, x_52);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_39);
lean_ctor_set(x_12, 3, x_54);
x_55 = lean_st_ref_set(x_4, x_12, x_14);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = lean_box(0);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_60 = lean_ctor_get(x_12, 0);
x_61 = lean_ctor_get(x_12, 1);
x_62 = lean_ctor_get(x_12, 2);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_12);
x_63 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
x_64 = lean_ctor_get(x_13, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_65 = x_13;
} else {
 lean_dec_ref(x_13);
 x_65 = lean_box(0);
}
x_66 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__2;
x_67 = l_Lean_Name_append(x_1, x_66);
x_68 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_68, 0, x_1);
x_69 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__4;
x_70 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__6;
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_10);
x_74 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__7;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_75);
lean_inc(x_6);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_6);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Std_PersistentArray_push___rarg(x_64, x_77);
if (lean_is_scalar(x_65)) {
 x_79 = lean_alloc_ctor(0, 1, 1);
} else {
 x_79 = x_65;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_63);
x_80 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_80, 0, x_60);
lean_ctor_set(x_80, 1, x_61);
lean_ctor_set(x_80, 2, x_62);
lean_ctor_set(x_80, 3, x_79);
x_81 = lean_st_ref_set(x_4, x_80, x_14);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_84 = lean_box(0);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_parenthesize___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_PrettyPrinter_parenthesize___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesize: uncaught backtrack exception");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesize___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_parenthesize___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesize___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_7 = l_Lean_Syntax_Traverser_fromSyntax(x_1);
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
x_12 = lean_st_ref_get(x_5, x_6);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_mk_ref(x_11, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_15);
x_17 = lean_apply_5(x_2, x_9, x_15, x_4, x_5, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_4);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_5, x_18);
lean_dec(x_5);
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
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_free_object(x_17);
lean_dec(x_30);
x_41 = l_Lean_PrettyPrinter_parenthesize___lambda__1___closed__2;
x_42 = l_Lean_throwError___at_Lean_PrettyPrinter_parenthesize___spec__1(x_41, x_4, x_5, x_36);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_5);
lean_dec(x_4);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_30);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_30);
x_48 = l_Lean_PrettyPrinter_parenthesize___lambda__1___closed__2;
x_49 = l_Lean_throwError___at_Lean_PrettyPrinter_parenthesize___spec__1(x_48, x_4, x_5, x_43);
lean_dec(x_5);
lean_dec(x_4);
return x_49;
}
}
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("input");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesize___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_2 = l_Lean_PrettyPrinter_parenthesize___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_6 = l_Lean_PrettyPrinter_parenthesize___closed__2;
x_24 = lean_st_ref_get(x_4, x_5);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 3);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get_uint8(x_26, sizeof(void*)*1);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = 0;
x_7 = x_29;
x_8 = x_28;
goto block_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_parenthesize___spec__3(x_6, x_3, x_4, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unbox(x_32);
lean_dec(x_32);
x_7 = x_34;
x_8 = x_33;
goto block_23;
}
block_23:
{
if (x_7 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_PrettyPrinter_parenthesize___lambda__1(x_2, x_1, x_9, x_3, x_4, x_8);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_box(0);
x_12 = 0;
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_14 = l_Lean_Syntax_formatStxAux(x_11, x_12, x_13, x_2);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__7;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_addTrace___at_Lean_PrettyPrinter_parenthesize___spec__2(x_6, x_18, x_3, x_4, x_8);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_PrettyPrinter_parenthesize___lambda__1(x_2, x_1, x_20, x_3, x_4, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_parenthesize___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_PrettyPrinter_parenthesize___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_parenthesize___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at_Lean_PrettyPrinter_parenthesize___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_parenthesize___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_1 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizeTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_PrettyPrinter_parenthesizeTerm___closed__1;
x_6 = l_Lean_PrettyPrinter_parenthesize(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizeTactic___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizeTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_PrettyPrinter_parenthesizeTactic___closed__1;
x_6 = l_Lean_PrettyPrinter_parenthesize(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizeCommand___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("command");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizeCommand___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_parenthesizeCommand___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizeCommand___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_parenthesizeCommand___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_parenthesizeCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_PrettyPrinter_parenthesizeCommand___closed__3;
x_6 = l_Lean_PrettyPrinter_parenthesize(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3449_(lean_object* x_1) {
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
LEAN_EXPORT lean_object* initialize_Lean_PrettyPrinter_Parenthesizer(lean_object* w) {
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
l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__4 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__4);
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
l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__14 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__14();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__14);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__15 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__15();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__15);
l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1___closed__1);
l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__1___closed__2);
l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__1 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__1();
l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__2 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__2);
l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__3 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__2___closed__3);
l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__4___closed__1 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__4___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__4___closed__1);
l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__7___closed__1 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__7___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___lambda__7___closed__1);
l_Lean_PrettyPrinter_parenthesizerAttribute___closed__1 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___closed__1);
l_Lean_PrettyPrinter_parenthesizerAttribute___closed__2 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___closed__2);
l_Lean_PrettyPrinter_parenthesizerAttribute___closed__3 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___closed__3);
l_Lean_PrettyPrinter_parenthesizerAttribute___closed__4 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___closed__4);
l_Lean_PrettyPrinter_parenthesizerAttribute___closed__5 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___closed__5);
l_Lean_PrettyPrinter_parenthesizerAttribute___closed__6 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___closed__6);
l_Lean_PrettyPrinter_parenthesizerAttribute___closed__7 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___closed__7);
l_Lean_PrettyPrinter_parenthesizerAttribute___closed__8 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___closed__8);
l_Lean_PrettyPrinter_parenthesizerAttribute___closed__9 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___closed__9);
l_Lean_PrettyPrinter_parenthesizerAttribute___closed__10 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___closed__10);
l_Lean_PrettyPrinter_parenthesizerAttribute___closed__11 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___closed__11);
l_Lean_PrettyPrinter_parenthesizerAttribute___closed__12 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___closed__12);
l_Lean_PrettyPrinter_parenthesizerAttribute___closed__13 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__13();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___closed__13);
l_Lean_PrettyPrinter_parenthesizerAttribute___closed__14 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__14();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___closed__14);
l_Lean_PrettyPrinter_parenthesizerAttribute___closed__15 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__15();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___closed__15);
l_Lean_PrettyPrinter_parenthesizerAttribute___closed__16 = _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__16();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute___closed__16);
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
l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__1 = _init_l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__1);
l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__2 = _init_l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__2);
l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__3 = _init_l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__3);
l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__4 = _init_l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__4);
l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__5 = _init_l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__5);
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
l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__6 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadTraverserParenthesizerM___closed__6);
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
l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__12 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__12);
l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__13 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__13();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__13);
l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__14 = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__14();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__14);
l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM = _init_l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM);
l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__1 = _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__1);
l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__2 = _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__2);
l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__3 = _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__3);
l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__4 = _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__4();
lean_mark_persistent(l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__4);
l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__5 = _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__5();
lean_mark_persistent(l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__5);
l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__6 = _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__6();
lean_mark_persistent(l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__6);
l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__7 = _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__7();
lean_mark_persistent(l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___closed__7);
l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__1 = _init_l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__1();
lean_mark_persistent(l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__1);
l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__2 = _init_l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__2();
lean_mark_persistent(l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__2);
l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__3 = _init_l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__3();
lean_mark_persistent(l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__3);
l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__4 = _init_l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__4();
lean_mark_persistent(l_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__4___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__5___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__5 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__5);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__6 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__6);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__7 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__7);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__8 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__8);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__9 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__9);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__10 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__10);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__11 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__11);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__12 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__12);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__13 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__13();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__13);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__14 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__14();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__14);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__15 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__15();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__15);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__16 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__16();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__16);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__17 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__17();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__17);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__18 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__18();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__18);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__19 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__19();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__19);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__20 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__20();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__10___closed__20);
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
l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__7 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__7);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__8 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__8);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__9 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__9);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__10 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__10);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__11 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__11);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__2___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__2___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__2___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__3);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__3 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__3);
res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__5 = _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__5);
l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__6 = _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__6);
l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3);
res = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3);
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
res = l_Lean_PrettyPrinter_Parenthesizer_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3227_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef);
lean_dec_ref(res);
l_Lean_PrettyPrinter_parenthesize___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_parenthesize___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesize___lambda__1___closed__1);
l_Lean_PrettyPrinter_parenthesize___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_parenthesize___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesize___lambda__1___closed__2);
l_Lean_PrettyPrinter_parenthesize___closed__1 = _init_l_Lean_PrettyPrinter_parenthesize___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesize___closed__1);
l_Lean_PrettyPrinter_parenthesize___closed__2 = _init_l_Lean_PrettyPrinter_parenthesize___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesize___closed__2);
l_Lean_PrettyPrinter_parenthesizeTerm___closed__1 = _init_l_Lean_PrettyPrinter_parenthesizeTerm___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizeTerm___closed__1);
l_Lean_PrettyPrinter_parenthesizeTactic___closed__1 = _init_l_Lean_PrettyPrinter_parenthesizeTactic___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizeTactic___closed__1);
l_Lean_PrettyPrinter_parenthesizeCommand___closed__1 = _init_l_Lean_PrettyPrinter_parenthesizeCommand___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizeCommand___closed__1);
l_Lean_PrettyPrinter_parenthesizeCommand___closed__2 = _init_l_Lean_PrettyPrinter_parenthesizeCommand___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizeCommand___closed__2);
l_Lean_PrettyPrinter_parenthesizeCommand___closed__3 = _init_l_Lean_PrettyPrinter_parenthesizeCommand___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizeCommand___closed__3);
res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_3449_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
