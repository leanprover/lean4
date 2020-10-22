// Lean compiler output
// Module: Lean.PrettyPrinter.Parenthesizer
// Imports: Init Lean.CoreM Lean.KeyedDeclsAttribute Lean.Parser.Extension Lean.ParserCompiler.Attribute Lean.PrettyPrinter.Backtrack
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
lean_object* l_Lean_PrettyPrinter_Lean_PrettyPrinter_Parenthesizer___instance__1(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer(lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___lambda__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PrettyPrinter_categoryParenthesizerAttribute;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesize___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__3;
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__4___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__8;
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__3;
extern lean_object* l_Lean_List_format___rarg___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_up(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__7;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__10;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer_match__1(lean_object*);
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Context_cat___default;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___boxed(lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__7;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_2344_(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3;
lean_object* l_Array_reverseAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withoutPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__20;
lean_object* l_ReaderT_Monad___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__15;
lean_object* l_Lean_PrettyPrinter_ParenthesizerM_orelse(lean_object*);
lean_object* l_ReaderT_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__18;
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Parser_leadPrec___closed__1;
extern lean_object* l_Std_Range___kind_term____x40_Init_Data_Range___hyg_111____closed__17;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__2;
lean_object* l_List_range(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_toggleInsideQuot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_parenthesizeCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_State_trailPrec___default;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedByCategoryToken_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer(lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__1;
lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__11;
lean_object* l_Lean_PrettyPrinter_Lean_PrettyPrinter_Parenthesizer___instance__1___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer___boxed(lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__17;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__3;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__2;
lean_object* l_Lean_PrettyPrinter_parenthesize___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__5;
lean_object* l_Lean_Syntax_Traverser_setCur(lean_object*, lean_object*);
extern lean_object* l_ULift_HasRepr___rarg___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute_match__1(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__7;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2;
extern lean_object* l_Lean_Option_format___rarg___closed__1;
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__5;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___spec__1(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ParenthesizerM_orelse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute_match__1(lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withForbidden_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__2(lean_object*);
lean_object* l_Lean_Unhygienic_run___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedByCategoryToken_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__12;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepBy1_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParserOfStack_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__3(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__21;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withoutForbidden_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__15;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__5;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__4;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM(lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
extern lean_object* l_Lean_Parser_maxPrec;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__11;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__1;
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__2;
lean_object* l_Lean_KeyedDeclsAttribute_getValues___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2;
lean_object* l_Lean_attrParamSyntaxToIdentifier(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__11;
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_State_contPrec___default;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__13;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_many1Unbox_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___lambda__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3;
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer(lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__12;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_eoi_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PrettyPrinter_Parenthesizer_State_visitedToken___default;
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__9;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___spec__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__4(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo___main(lean_object*);
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___spec__2(lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__9;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__4;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__19;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_down(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__2;
lean_object* l_StateRefT_x27_get___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer(lean_object*);
uint8_t l_Lean_Parser_isParserCategory(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__2(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedByCategoryToken_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__10;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_fmt___at_Lean_Level_LevelToFormat_Result_format___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__2;
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_right(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Unhygienic_Lean_Hygiene___instance__1___closed__4;
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_paren___closed__2;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__6;
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_throwError___spec__1(lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_Lean_CoreM___instance__6___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withForbidden_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1;
lean_object* l_Lean_PrettyPrinter_parenthesize_match__1(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_paren___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeCommand___closed__1;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1;
lean_object* l_Lean_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__5;
lean_object* l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_PUnit_Inhabited;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwError(lean_object*);
extern lean_object* l_Lean_Option_format___rarg___closed__3;
lean_object* l_Lean_PrettyPrinter_parenthesize_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__16;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_optional_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_skip_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(lean_object*);
extern lean_object* l_Lean_ParserCompiler_CombinatorAttribute_Lean_ParserCompiler_Attribute___instance__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___rarg(lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_throwError___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_State_contCat___default;
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__6;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
extern lean_object* l_Lean_Format_paren___closed__3;
extern lean_object* l_Lean_KeyedDeclsAttribute_Lean_KeyedDeclsAttribute___instance__3___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3;
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withForbidden_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_State_minPrec___default;
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2_match__1(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_throwError___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_min(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_many1_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__3;
extern lean_object* l_Lean_PrettyPrinter_backtrackExceptionId;
lean_object* l_Lean_PrettyPrinter_parenthesizeTerm___closed__1;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_inhabited___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1;
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__4;
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParserOfStack_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute(lean_object*);
lean_object* l_List_forM___main___at_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__5(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_error_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesize___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Substring_splitOnAux___main___closed__2;
lean_object* l___private_Init_Util_2__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_interpolatedStrLitKind;
extern lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__7;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_liftCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_try_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_antiquot_parenthesizer(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer(lean_object*, lean_object*, lean_object*);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_st_ref_get(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_11, 1);
x_19 = lean_ctor_get(x_11, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
x_21 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_22 = lean_nat_dec_eq(x_21, x_20);
lean_dec(x_20);
if (x_22 == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_11);
lean_dec(x_12);
x_23 = lean_st_ref_set(x_4, x_9, x_18);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_dec(x_11);
x_27 = lean_ctor_get(x_12, 0);
lean_inc(x_27);
x_28 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_29 = lean_nat_dec_eq(x_28, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_12);
x_31 = lean_st_ref_set(x_4, x_9, x_26);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_32);
return x_33;
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
static lean_object* _init_l_Lean_PrettyPrinter_Lean_PrettyPrinter_Parenthesizer___instance__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ParenthesizerM_orelse___rarg), 7, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Lean_PrettyPrinter_Parenthesizer___instance__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Lean_PrettyPrinter_Parenthesizer___instance__1___closed__1;
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkParenthesizerAttribute_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [parenthesizer] argument, expected identifier");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [parenthesizer] argument, unknown syntax kind '");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_attrParamSyntaxToIdentifier(x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
x_13 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3;
x_14 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_13, x_3, x_4, x_5, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
if (x_1 == 0)
{
lean_object* x_29; 
x_29 = lean_box(0);
x_16 = x_29;
goto block_28;
}
else
{
lean_object* x_30; 
lean_inc(x_15);
lean_inc(x_11);
x_30 = lean_environment_find(x_11, x_15);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_box(0);
x_16 = x_31;
goto block_28;
}
else
{
lean_object* x_32; 
lean_dec(x_30);
lean_dec(x_11);
lean_dec(x_10);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_9);
return x_32;
}
}
block_28:
{
uint8_t x_17; 
lean_dec(x_16);
x_17 = l_Lean_Parser_isValidSyntaxNodeKind(x_11, x_15);
lean_dec(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
x_18 = l_System_FilePath_dirName___closed__1;
x_19 = l_Lean_Name_toStringWithSep___main(x_18, x_15);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__6;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__8;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_25, x_3, x_4, x_5, x_9);
return x_26;
}
else
{
lean_object* x_27; 
if (lean_is_scalar(x_10)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_10;
}
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
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
x_1 = l_Lean_mkAppStx___closed__2;
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
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___boxed), 6, 0);
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
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute_match__1___rarg), 3, 0);
return x_2;
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
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_attrParamSyntaxToIdentifier(x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_free_object(x_7);
x_13 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3;
x_14 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_13, x_3, x_4, x_5, x_10);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Parser_isParserCategory(x_11, x_15);
lean_dec(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_7);
x_17 = l_System_FilePath_dirName___closed__1;
x_18 = l_Lean_Name_toStringWithSep___main(x_17, x_15);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__3;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__8;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_24, x_3, x_4, x_5, x_10);
return x_25;
}
else
{
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_attrParamSyntaxToIdentifier(x_2);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_28);
x_30 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3;
x_31 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_30, x_3, x_4, x_5, x_27);
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
x_33 = l_Lean_Parser_isParserCategory(x_28, x_32);
lean_dec(x_28);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = l_System_FilePath_dirName___closed__1;
x_35 = l_Lean_Name_toStringWithSep___main(x_34, x_32);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__3;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__8;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_41, x_3, x_4, x_5, x_27);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_32);
lean_ctor_set(x_43, 1, x_27);
return x_43;
}
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
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___boxed), 6, 0);
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
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2_match__1___rarg), 2, 0);
return x_3;
}
}
lean_object* l_StateRefT_x27_get___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___spec__2___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_1);
x_12 = lean_st_ref_set(x_3, x_8, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 3);
x_22 = lean_ctor_get(x_8, 4);
x_23 = lean_ctor_get_uint8(x_8, sizeof(void*)*5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_24 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*5, x_23);
x_25 = lean_st_ref_set(x_3, x_24, x_9);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_apply_1(x_2, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_9, 0, x_15);
x_16 = lean_st_ref_set(x_4, x_9, x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
x_23 = lean_ctor_get(x_9, 2);
x_24 = lean_ctor_get(x_9, 3);
x_25 = lean_ctor_get(x_9, 4);
x_26 = lean_ctor_get_uint8(x_9, sizeof(void*)*5);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_27 = lean_apply_1(x_2, x_21);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_25);
lean_ctor_set_uint8(x_30, sizeof(void*)*5, x_26);
x_31 = lean_st_ref_set(x_4, x_30, x_10);
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
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_get___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___spec__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__1;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__3;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___lambda__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___lambda__3___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__4;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__5;
x_3 = l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__7;
return x_1;
}
}
lean_object* l_StateRefT_x27_get___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_StateRefT_x27_get___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 3);
x_13 = lean_ctor_get(x_8, 1);
lean_dec(x_13);
x_14 = l_Nat_min(x_1, x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_inc(x_15);
lean_ctor_set(x_8, 3, x_15);
lean_ctor_set(x_8, 1, x_15);
x_16 = lean_st_ref_set(x_3, x_8, x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = l_Nat_min(x_24, x_1);
lean_dec(x_24);
lean_ctor_set(x_12, 0, x_25);
lean_ctor_set(x_8, 1, x_15);
x_26 = lean_st_ref_set(x_3, x_8, x_10);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_12, 0);
lean_inc(x_33);
lean_dec(x_12);
x_34 = l_Nat_min(x_33, x_1);
lean_dec(x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_8, 3, x_35);
lean_ctor_set(x_8, 1, x_15);
x_36 = lean_st_ref_set(x_3, x_8, x_10);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_8, 0);
x_42 = lean_ctor_get(x_8, 2);
x_43 = lean_ctor_get(x_8, 3);
x_44 = lean_ctor_get(x_8, 4);
x_45 = lean_ctor_get_uint8(x_8, sizeof(void*)*5);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_8);
x_46 = l_Nat_min(x_1, x_1);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_inc(x_47);
x_48 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_42);
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set(x_48, 4, x_44);
lean_ctor_set_uint8(x_48, sizeof(void*)*5, x_45);
x_49 = lean_st_ref_set(x_3, x_48, x_10);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = lean_box(0);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_54 = lean_ctor_get(x_43, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_55 = x_43;
} else {
 lean_dec_ref(x_43);
 x_55 = lean_box(0);
}
x_56 = l_Nat_min(x_54, x_1);
lean_dec(x_54);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_58, 0, x_41);
lean_ctor_set(x_58, 1, x_47);
lean_ctor_set(x_58, 2, x_42);
lean_ctor_set(x_58, 3, x_57);
lean_ctor_set(x_58, 4, x_44);
lean_ctor_set_uint8(x_58, sizeof(void*)*5, x_45);
x_59 = lean_st_ref_set(x_3, x_58, x_10);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_7, 1);
lean_inc(x_64);
lean_dec(x_7);
x_65 = !lean_is_exclusive(x_8);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_8, 3);
x_67 = lean_ctor_get(x_8, 1);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_9);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_9, 0);
x_70 = l_Nat_min(x_69, x_1);
lean_dec(x_69);
lean_ctor_set(x_9, 0, x_70);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = l_Nat_min(x_1, x_1);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_8, 3, x_72);
x_73 = lean_st_ref_set(x_3, x_8, x_64);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
x_76 = lean_box(0);
lean_ctor_set(x_73, 0, x_76);
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_66);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_66, 0);
x_82 = l_Nat_min(x_81, x_1);
lean_dec(x_81);
lean_ctor_set(x_66, 0, x_82);
x_83 = lean_st_ref_set(x_3, x_8, x_64);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_83, 0);
lean_dec(x_85);
x_86 = lean_box(0);
lean_ctor_set(x_83, 0, x_86);
return x_83;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_dec(x_83);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = lean_ctor_get(x_66, 0);
lean_inc(x_90);
lean_dec(x_66);
x_91 = l_Nat_min(x_90, x_1);
lean_dec(x_90);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_8, 3, x_92);
x_93 = lean_st_ref_set(x_3, x_8, x_64);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
x_96 = lean_box(0);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_9, 0);
lean_inc(x_98);
lean_dec(x_9);
x_99 = l_Nat_min(x_98, x_1);
lean_dec(x_98);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_101 = l_Nat_min(x_1, x_1);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_8, 3, x_102);
lean_ctor_set(x_8, 1, x_100);
x_103 = lean_st_ref_set(x_3, x_8, x_64);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = lean_box(0);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_108 = lean_ctor_get(x_66, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_109 = x_66;
} else {
 lean_dec_ref(x_66);
 x_109 = lean_box(0);
}
x_110 = l_Nat_min(x_108, x_1);
lean_dec(x_108);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(1, 1, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_8, 3, x_111);
lean_ctor_set(x_8, 1, x_100);
x_112 = lean_st_ref_set(x_3, x_8, x_64);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
x_115 = lean_box(0);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_117 = lean_ctor_get(x_8, 0);
x_118 = lean_ctor_get(x_8, 2);
x_119 = lean_ctor_get(x_8, 3);
x_120 = lean_ctor_get(x_8, 4);
x_121 = lean_ctor_get_uint8(x_8, sizeof(void*)*5);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_8);
x_122 = lean_ctor_get(x_9, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_123 = x_9;
} else {
 lean_dec_ref(x_9);
 x_123 = lean_box(0);
}
x_124 = l_Nat_min(x_122, x_1);
lean_dec(x_122);
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(1, 1, 0);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_124);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_126 = l_Nat_min(x_1, x_1);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_128, 0, x_117);
lean_ctor_set(x_128, 1, x_125);
lean_ctor_set(x_128, 2, x_118);
lean_ctor_set(x_128, 3, x_127);
lean_ctor_set(x_128, 4, x_120);
lean_ctor_set_uint8(x_128, sizeof(void*)*5, x_121);
x_129 = lean_st_ref_set(x_3, x_128, x_64);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_131 = x_129;
} else {
 lean_dec_ref(x_129);
 x_131 = lean_box(0);
}
x_132 = lean_box(0);
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_130);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_134 = lean_ctor_get(x_119, 0);
lean_inc(x_134);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_135 = x_119;
} else {
 lean_dec_ref(x_119);
 x_135 = lean_box(0);
}
x_136 = l_Nat_min(x_134, x_1);
lean_dec(x_134);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(1, 1, 0);
} else {
 x_137 = x_135;
}
lean_ctor_set(x_137, 0, x_136);
x_138 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_138, 0, x_117);
lean_ctor_set(x_138, 1, x_125);
lean_ctor_set(x_138, 2, x_118);
lean_ctor_set(x_138, 3, x_137);
lean_ctor_set(x_138, 4, x_120);
lean_ctor_set_uint8(x_138, sizeof(void*)*5, x_121);
x_139 = lean_st_ref_set(x_3, x_138, x_64);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_141 = x_139;
} else {
 lean_dec_ref(x_139);
 x_141 = lean_box(0);
}
x_142 = lean_box(0);
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_140);
return x_143;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_Syntax_Traverser_left(x_9);
lean_ctor_set(x_6, 0, x_10);
x_11 = lean_st_ref_set(x_1, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get_uint8(x_6, sizeof(void*)*5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_24 = l_Lean_Syntax_Traverser_left(x_18);
x_25 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_25, 4, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*5, x_23);
x_26 = lean_st_ref_set(x_1, x_25, x_7);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
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
x_12 = l_Lean_Syntax_Traverser_down(x_11, x_1);
lean_ctor_set(x_8, 0, x_12);
x_13 = lean_st_ref_set(x_3, x_8, x_9);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 2);
x_23 = lean_ctor_get(x_8, 3);
x_24 = lean_ctor_get(x_8, 4);
x_25 = lean_ctor_get_uint8(x_8, sizeof(void*)*5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_26 = l_Lean_Syntax_Traverser_down(x_20, x_1);
x_27 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_25);
x_28 = lean_st_ref_set(x_3, x_27, x_9);
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
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_Syntax_Traverser_up(x_9);
lean_ctor_set(x_6, 0, x_10);
x_11 = lean_st_ref_set(x_1, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get_uint8(x_6, sizeof(void*)*5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_24 = l_Lean_Syntax_Traverser_up(x_18);
x_25 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_25, 4, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*5, x_23);
x_26 = lean_st_ref_set(x_1, x_25, x_7);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
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
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___spec__1___rarg___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___spec__1___rarg___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___lambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__1;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__2;
x_3 = l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__4;
return x_1;
}
}
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize_match__2___rarg), 4, 0);
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
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
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_dec(x_1);
x_9 = lean_box(x_8);
x_10 = lean_apply_6(x_2, x_7, x_3, x_4, x_5, x_6, x_9);
return x_10;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_box(x_10);
x_13 = lean_apply_6(x_2, x_11, x_9, x_6, x_7, x_8, x_12);
return x_13;
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
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(x_9);
lean_dec(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
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
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_Lean_addMessageContextPartial___at_Lean_Core_Lean_CoreM___instance__6___spec__1(x_2, x_5, x_6, x_7);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_10);
lean_inc(x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Std_PersistentArray_push___rarg(x_19, x_21);
lean_ctor_set(x_14, 0, x_22);
x_23 = lean_st_ref_set(x_6, x_13, x_15);
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
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_10);
lean_inc(x_8);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Std_PersistentArray_push___rarg(x_31, x_33);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_30);
lean_ctor_set(x_13, 3, x_35);
x_36 = lean_st_ref_set(x_6, x_13, x_15);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
x_43 = lean_ctor_get(x_13, 2);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
x_44 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
x_45 = lean_ctor_get(x_14, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_46 = x_14;
} else {
 lean_dec_ref(x_14);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_10);
lean_inc(x_8);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_8);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Std_PersistentArray_push___rarg(x_45, x_48);
if (lean_is_scalar(x_46)) {
 x_50 = lean_alloc_ctor(0, 1, 1);
} else {
 x_50 = x_46;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_44);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_42);
lean_ctor_set(x_51, 2, x_43);
lean_ctor_set(x_51, 3, x_50);
x_52 = lean_st_ref_set(x_6, x_51, x_15);
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
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
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
x_12 = l_Lean_Syntax_Traverser_setCur(x_11, x_1);
lean_ctor_set(x_8, 0, x_12);
x_13 = lean_st_ref_set(x_3, x_8, x_9);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 2);
x_23 = lean_ctor_get(x_8, 3);
x_24 = lean_ctor_get(x_8, 4);
x_25 = lean_ctor_get_uint8(x_8, sizeof(void*)*5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_26 = l_Lean_Syntax_Traverser_setCur(x_20, x_1);
x_27 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_25);
x_28 = lean_st_ref_set(x_3, x_27, x_9);
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
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_Syntax_Traverser_right(x_9);
lean_ctor_set(x_6, 0, x_10);
x_11 = lean_st_ref_set(x_1, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get_uint8(x_6, sizeof(void*)*5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_24 = l_Lean_Syntax_Traverser_right(x_18);
x_25 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_25, 4, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*5, x_23);
x_26 = lean_st_ref_set(x_1, x_25, x_7);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Option_format___rarg___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_fmt___at_Lean_Level_LevelToFormat_Result_format___spec__1(x_3);
x_5 = l_Lean_Option_format___rarg___closed__3;
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
}
lean_object* l_Lean_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__7(x_2);
x_5 = l_Lean_List_format___rarg___closed__2;
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_System_FilePath_dirName___closed__1;
x_10 = l_Lean_Name_toStringWithSep___main(x_9, x_3);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Format_paren___closed__3;
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Format_paren___closed__4;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Format_paren___closed__2;
x_18 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = 0;
x_20 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
return x_20;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_st_ref_get(x_7, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (x_1 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_12, 4);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_2);
x_16 = lean_st_ref_take(x_7, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_17, 4);
lean_dec(x_20);
x_21 = lean_ctor_get(x_17, 3);
lean_dec(x_21);
lean_ctor_set(x_17, 4, x_15);
lean_ctor_set(x_17, 3, x_3);
x_22 = lean_st_ref_set(x_7, x_17, x_18);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
x_31 = lean_ctor_get(x_17, 2);
x_32 = lean_ctor_get_uint8(x_17, sizeof(void*)*5);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_33 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set(x_33, 3, x_3);
lean_ctor_set(x_33, 4, x_15);
lean_ctor_set_uint8(x_33, sizeof(void*)*5, x_32);
x_34 = lean_st_ref_set(x_7, x_33, x_18);
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
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
lean_dec(x_11);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_13, 0);
x_42 = l_Nat_min(x_41, x_2);
lean_dec(x_2);
lean_dec(x_41);
lean_ctor_set(x_13, 0, x_42);
x_43 = lean_st_ref_take(x_7, x_39);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_44, 4);
lean_dec(x_47);
x_48 = lean_ctor_get(x_44, 3);
lean_dec(x_48);
lean_ctor_set(x_44, 4, x_13);
lean_ctor_set(x_44, 3, x_3);
x_49 = lean_st_ref_set(x_7, x_44, x_45);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_56 = lean_ctor_get(x_44, 0);
x_57 = lean_ctor_get(x_44, 1);
x_58 = lean_ctor_get(x_44, 2);
x_59 = lean_ctor_get_uint8(x_44, sizeof(void*)*5);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_44);
x_60 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set(x_60, 3, x_3);
lean_ctor_set(x_60, 4, x_13);
lean_ctor_set_uint8(x_60, sizeof(void*)*5, x_59);
x_61 = lean_st_ref_set(x_7, x_60, x_45);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_66 = lean_ctor_get(x_13, 0);
lean_inc(x_66);
lean_dec(x_13);
x_67 = l_Nat_min(x_66, x_2);
lean_dec(x_2);
lean_dec(x_66);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_st_ref_take(x_7, x_39);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_70, 2);
lean_inc(x_74);
x_75 = lean_ctor_get_uint8(x_70, sizeof(void*)*5);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 lean_ctor_release(x_70, 2);
 lean_ctor_release(x_70, 3);
 lean_ctor_release(x_70, 4);
 x_76 = x_70;
} else {
 lean_dec_ref(x_70);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 5, 1);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_74);
lean_ctor_set(x_77, 3, x_3);
lean_ctor_set(x_77, 4, x_68);
lean_ctor_set_uint8(x_77, sizeof(void*)*5, x_75);
x_78 = lean_st_ref_set(x_7, x_77, x_71);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
x_81 = lean_box(0);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec(x_12);
lean_dec(x_2);
x_83 = lean_ctor_get(x_11, 1);
lean_inc(x_83);
lean_dec(x_11);
x_84 = lean_st_ref_take(x_7, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = !lean_is_exclusive(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_ctor_get(x_85, 4);
lean_dec(x_88);
x_89 = lean_ctor_get(x_85, 3);
lean_dec(x_89);
lean_ctor_set(x_85, 4, x_4);
lean_ctor_set(x_85, 3, x_3);
x_90 = lean_st_ref_set(x_7, x_85, x_86);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_90, 0);
lean_dec(x_92);
x_93 = lean_box(0);
lean_ctor_set(x_90, 0, x_93);
return x_90;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_97 = lean_ctor_get(x_85, 0);
x_98 = lean_ctor_get(x_85, 1);
x_99 = lean_ctor_get(x_85, 2);
x_100 = lean_ctor_get_uint8(x_85, sizeof(void*)*5);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_85);
x_101 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set(x_101, 2, x_99);
lean_ctor_set(x_101, 3, x_3);
lean_ctor_set(x_101, 4, x_4);
lean_ctor_set_uint8(x_101, sizeof(void*)*5, x_100);
x_102 = lean_st_ref_set(x_7, x_101, x_86);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_box(0);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_maxPrec;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesized: ");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_36 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_7, x_8, x_9, x_10);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_50 = lean_st_ref_get(x_9, x_38);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 3);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get_uint8(x_52, sizeof(void*)*1);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = 0;
x_39 = x_55;
x_40 = x_54;
goto block_49;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_dec(x_50);
lean_inc(x_4);
x_57 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_4, x_6, x_7, x_8, x_9, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unbox(x_58);
lean_dec(x_58);
x_39 = x_60;
x_40 = x_59;
goto block_49;
}
block_35:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_7, x_8, x_9, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_take(x_7, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_15, 4);
lean_dec(x_18);
x_19 = lean_ctor_get(x_15, 2);
lean_dec(x_19);
x_20 = lean_ctor_get(x_15, 1);
lean_dec(x_20);
x_21 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__1;
lean_ctor_set(x_15, 4, x_2);
lean_ctor_set(x_15, 2, x_1);
lean_ctor_set(x_15, 1, x_21);
x_22 = lean_st_ref_set(x_7, x_15, x_16);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = lean_apply_6(x_3, x_24, x_6, x_7, x_8, x_9, x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 3);
x_28 = lean_ctor_get_uint8(x_15, sizeof(void*)*5);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__1;
x_30 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_1);
lean_ctor_set(x_30, 3, x_27);
lean_ctor_set(x_30, 4, x_2);
lean_ctor_set_uint8(x_30, sizeof(void*)*5, x_28);
x_31 = lean_st_ref_set(x_7, x_30, x_16);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = lean_apply_6(x_3, x_33, x_6, x_7, x_8, x_9, x_32);
return x_34;
}
}
block_49:
{
if (x_39 == 0)
{
lean_dec(x_37);
lean_dec(x_4);
x_11 = x_40;
goto block_35;
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = 0;
x_42 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_43 = l_Lean_Syntax_formatStxAux(x_2, x_41, x_42, x_37);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__4;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_4, x_46, x_6, x_7, x_8, x_9, x_40);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_11 = x_48;
goto block_35;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Substring_splitOnAux___main___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Syntax_getHeadInfo___main(x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_apply_1(x_5, x_13);
x_17 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_16, x_7, x_8, x_9, x_10, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_1, x_2, x_3, x_4, x_18, x_7, x_8, x_9, x_10, x_19);
lean_dec(x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = l_Lean_Syntax_getTailInfo(x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_21);
x_23 = lean_apply_1(x_5, x_13);
x_24 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_23, x_7, x_8, x_9, x_10, x_14);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_1, x_2, x_3, x_4, x_25, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_25);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
lean_dec(x_22);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
x_32 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1;
lean_inc(x_31);
lean_ctor_set(x_21, 0, x_32);
x_33 = l_Lean_Syntax_setHeadInfo(x_13, x_21);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_35 = lean_ctor_get(x_28, 1);
x_36 = lean_ctor_get(x_28, 2);
lean_inc(x_35);
lean_ctor_set(x_28, 2, x_32);
x_37 = l_Lean_Syntax_setTailInfo(x_33, x_28);
x_38 = lean_apply_1(x_5, x_37);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_31);
lean_ctor_set(x_39, 2, x_32);
x_40 = l_Lean_Syntax_setHeadInfo(x_38, x_39);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_32);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 2, x_36);
x_42 = l_Lean_Syntax_setTailInfo(x_40, x_41);
x_43 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_42, x_7, x_8, x_9, x_10, x_14);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_1, x_2, x_3, x_4, x_44, x_7, x_8, x_9, x_10, x_45);
lean_dec(x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_47 = lean_ctor_get(x_28, 0);
x_48 = lean_ctor_get(x_28, 1);
x_49 = lean_ctor_get(x_28, 2);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_28);
lean_inc(x_48);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set(x_50, 2, x_32);
x_51 = l_Lean_Syntax_setTailInfo(x_33, x_50);
x_52 = lean_apply_1(x_5, x_51);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_30);
lean_ctor_set(x_53, 1, x_31);
lean_ctor_set(x_53, 2, x_32);
x_54 = l_Lean_Syntax_setHeadInfo(x_52, x_53);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_32);
lean_ctor_set(x_55, 1, x_48);
lean_ctor_set(x_55, 2, x_49);
x_56 = l_Lean_Syntax_setTailInfo(x_54, x_55);
x_57 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_56, x_7, x_8, x_9, x_10, x_14);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_1, x_2, x_3, x_4, x_58, x_7, x_8, x_9, x_10, x_59);
lean_dec(x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_61 = lean_ctor_get(x_21, 0);
x_62 = lean_ctor_get(x_21, 1);
x_63 = lean_ctor_get(x_21, 2);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_21);
x_64 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1;
lean_inc(x_62);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
lean_ctor_set(x_65, 2, x_63);
x_66 = l_Lean_Syntax_setHeadInfo(x_13, x_65);
x_67 = lean_ctor_get(x_28, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_28, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_28, 2);
lean_inc(x_69);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 x_70 = x_28;
} else {
 lean_dec_ref(x_28);
 x_70 = lean_box(0);
}
lean_inc(x_68);
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 3, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_68);
lean_ctor_set(x_71, 2, x_64);
x_72 = l_Lean_Syntax_setTailInfo(x_66, x_71);
x_73 = lean_apply_1(x_5, x_72);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_61);
lean_ctor_set(x_74, 1, x_62);
lean_ctor_set(x_74, 2, x_64);
x_75 = l_Lean_Syntax_setHeadInfo(x_73, x_74);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_64);
lean_ctor_set(x_76, 1, x_68);
lean_ctor_set(x_76, 2, x_69);
x_77 = l_Lean_Syntax_setTailInfo(x_75, x_76);
x_78 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_77, x_7, x_8, x_9, x_10, x_14);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_1, x_2, x_3, x_4, x_79, x_7, x_8, x_9, x_10, x_80);
lean_dec(x_79);
return x_81;
}
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1;
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesize");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__2;
x_2 = l_PUnit_Inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6;
x_2 = lean_alloc_closure((void*)(l_ReaderT_inhabited___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.PrettyPrinter.Parenthesizer");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.PrettyPrinter.Parenthesizer.maybeParenthesize");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maybeParenthesize: visited a syntax tree without precedences?!");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__8;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__9;
x_3 = lean_unsigned_to_nat(212u);
x_4 = lean_unsigned_to_nat(6u);
x_5 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
x_6 = l___private_Init_Util_2__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("...precedences are ");
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
x_1 = lean_mk_string(" >? ");
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
x_1 = l_List_reprAux___main___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" <=? ");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__17;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesizing (cont := ");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__19;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_ULift_HasRepr___rarg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg(x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_6, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_111; lean_object* x_112; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_17, 2);
x_22 = lean_ctor_get(x_17, 3);
x_23 = lean_ctor_get(x_17, 4);
x_24 = lean_ctor_get_uint8(x_17, sizeof(void*)*5);
x_25 = lean_box(0);
x_26 = lean_box(0);
x_27 = 0;
lean_ctor_set(x_17, 4, x_25);
lean_ctor_set(x_17, 3, x_25);
lean_ctor_set(x_17, 2, x_26);
lean_ctor_set(x_17, 1, x_25);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_27);
x_28 = lean_st_ref_set(x_6, x_17, x_18);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_150 = lean_st_ref_get(x_8, x_29);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_151, 3);
lean_inc(x_152);
lean_dec(x_151);
x_153 = lean_ctor_get_uint8(x_152, sizeof(void*)*1);
lean_dec(x_152);
if (x_153 == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_150, 1);
lean_inc(x_154);
lean_dec(x_150);
x_111 = x_27;
x_112 = x_154;
goto block_149;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_155 = lean_ctor_get(x_150, 1);
lean_inc(x_155);
lean_dec(x_150);
x_156 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_157 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_156, x_5, x_6, x_7, x_8, x_155);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_unbox(x_158);
lean_dec(x_158);
x_111 = x_160;
x_112 = x_159;
goto block_149;
}
block_110:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 3);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_30);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__7;
x_34 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__11;
x_35 = lean_panic_fn(x_33, x_34);
x_36 = lean_apply_5(x_35, x_5, x_6, x_7, x_8, x_31);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_70; lean_object* x_71; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_37 = lean_ctor_get(x_30, 4);
lean_inc(x_37);
lean_dec(x_30);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec(x_32);
x_99 = lean_st_ref_get(x_8, x_31);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 3);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_ctor_get_uint8(x_101, sizeof(void*)*1);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
lean_dec(x_99);
x_70 = x_27;
x_71 = x_103;
goto block_98;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
lean_dec(x_99);
x_105 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_106 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_105, x_5, x_6, x_7, x_8, x_104);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_unbox(x_107);
lean_dec(x_107);
x_70 = x_109;
x_71 = x_108;
goto block_98;
}
block_69:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_54; 
x_40 = lean_box(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_3);
x_41 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1___boxed), 10, 4);
lean_closure_set(x_41, 0, x_40);
lean_closure_set(x_41, 1, x_3);
lean_closure_set(x_41, 2, x_22);
lean_closure_set(x_41, 3, x_23);
x_54 = lean_nat_dec_lt(x_38, x_3);
lean_dec(x_38);
if (x_54 == 0)
{
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_41);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_box(0);
x_56 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(x_24, x_3, x_22, x_23, x_55, x_5, x_6, x_7, x_8, x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_56;
}
else
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_box(0);
x_58 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(x_24, x_3, x_22, x_23, x_57, x_5, x_6, x_7, x_8, x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_37, 0);
lean_inc(x_59);
lean_dec(x_37);
x_60 = lean_ctor_get(x_20, 0);
lean_inc(x_60);
lean_dec(x_20);
x_61 = lean_name_eq(x_1, x_21);
lean_dec(x_21);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_box(0);
x_63 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(x_24, x_3, x_22, x_23, x_62, x_5, x_6, x_7, x_8, x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_63;
}
else
{
uint8_t x_64; 
x_64 = lean_nat_dec_le(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_box(0);
x_66 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(x_24, x_3, x_22, x_23, x_65, x_5, x_6, x_7, x_8, x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_66;
}
else
{
lean_object* x_67; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
x_67 = lean_box(0);
x_42 = x_67;
goto block_53;
}
}
}
}
}
else
{
lean_object* x_68; 
lean_dec(x_37);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_68 = lean_box(0);
x_42 = x_68;
goto block_53;
}
block_53:
{
lean_object* x_43; uint8_t x_44; 
lean_dec(x_42);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_nat_dec_lt(x_43, x_14);
lean_dec(x_14);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_46 = lean_box(0);
x_47 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3(x_1, x_25, x_41, x_45, x_2, x_46, x_5, x_6, x_7, x_8, x_39);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___rarg(x_6, x_7, x_8, x_39);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_52 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3(x_1, x_25, x_41, x_51, x_2, x_49, x_5, x_6, x_7, x_8, x_50);
lean_dec(x_49);
return x_52;
}
}
}
block_98:
{
if (x_70 == 0)
{
x_39 = x_71;
goto block_69;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_inc(x_3);
x_72 = l_Lean_fmt___at_Lean_Level_LevelToFormat_Result_format___spec__1(x_3);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__15;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
lean_inc(x_38);
x_78 = l_Lean_fmt___at_Lean_Level_LevelToFormat_Result_format___spec__1(x_38);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__16;
x_82 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
lean_inc(x_1);
lean_inc(x_37);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_37);
lean_ctor_set(x_83, 1, x_1);
x_84 = l_Lean_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_83);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__18;
x_88 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
lean_inc(x_21);
lean_inc(x_20);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_20);
lean_ctor_set(x_89, 1, x_21);
x_90 = l_Lean_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_89);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_94 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_96 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_95, x_94, x_5, x_6, x_7, x_8, x_71);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_39 = x_97;
goto block_69;
}
}
}
}
block_149:
{
if (x_111 == 0)
{
lean_object* x_113; 
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_113 = lean_apply_5(x_4, x_5, x_6, x_7, x_8, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_115 = lean_st_ref_get(x_6, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_30 = x_116;
x_31 = x_117;
goto block_110;
}
else
{
uint8_t x_118; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_113);
if (x_118 == 0)
{
return x_113;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_113, 0);
x_120 = lean_ctor_get(x_113, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_113);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_inc(x_21);
lean_inc(x_20);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_20);
lean_ctor_set(x_122, 1, x_21);
x_123 = l_Lean_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_122);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__20;
x_126 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__21;
x_128 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_11);
x_130 = l_Lean_MessageData_ofList___closed__3;
x_131 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = lean_unsigned_to_nat(2u);
x_133 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
x_134 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_134, 0, x_128);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_136 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_138 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_137, x_136, x_5, x_6, x_7, x_8, x_112);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_140 = lean_apply_5(x_4, x_5, x_6, x_7, x_8, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_st_ref_get(x_6, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_30 = x_143;
x_31 = x_144;
goto block_110;
}
else
{
uint8_t x_145; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = !lean_is_exclusive(x_140);
if (x_145 == 0)
{
return x_140;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_140, 0);
x_147 = lean_ctor_get(x_140, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_140);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_254; lean_object* x_255; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_161 = lean_ctor_get(x_17, 0);
x_162 = lean_ctor_get(x_17, 1);
x_163 = lean_ctor_get(x_17, 2);
x_164 = lean_ctor_get(x_17, 3);
x_165 = lean_ctor_get(x_17, 4);
x_166 = lean_ctor_get_uint8(x_17, sizeof(void*)*5);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_17);
x_167 = lean_box(0);
x_168 = lean_box(0);
x_169 = 0;
x_170 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_170, 0, x_161);
lean_ctor_set(x_170, 1, x_167);
lean_ctor_set(x_170, 2, x_168);
lean_ctor_set(x_170, 3, x_167);
lean_ctor_set(x_170, 4, x_167);
lean_ctor_set_uint8(x_170, sizeof(void*)*5, x_169);
x_171 = lean_st_ref_set(x_6, x_170, x_18);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec(x_171);
x_293 = lean_st_ref_get(x_8, x_172);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_294, 3);
lean_inc(x_295);
lean_dec(x_294);
x_296 = lean_ctor_get_uint8(x_295, sizeof(void*)*1);
lean_dec(x_295);
if (x_296 == 0)
{
lean_object* x_297; 
x_297 = lean_ctor_get(x_293, 1);
lean_inc(x_297);
lean_dec(x_293);
x_254 = x_169;
x_255 = x_297;
goto block_292;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_298 = lean_ctor_get(x_293, 1);
lean_inc(x_298);
lean_dec(x_293);
x_299 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_300 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_299, x_5, x_6, x_7, x_8, x_298);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = lean_unbox(x_301);
lean_dec(x_301);
x_254 = x_303;
x_255 = x_302;
goto block_292;
}
block_253:
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_173, 3);
lean_inc(x_175);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_173);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_176 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__7;
x_177 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__11;
x_178 = lean_panic_fn(x_176, x_177);
x_179 = lean_apply_5(x_178, x_5, x_6, x_7, x_8, x_174);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_213; lean_object* x_214; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_180 = lean_ctor_get(x_173, 4);
lean_inc(x_180);
lean_dec(x_173);
x_181 = lean_ctor_get(x_175, 0);
lean_inc(x_181);
lean_dec(x_175);
x_242 = lean_st_ref_get(x_8, x_174);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_243, 3);
lean_inc(x_244);
lean_dec(x_243);
x_245 = lean_ctor_get_uint8(x_244, sizeof(void*)*1);
lean_dec(x_244);
if (x_245 == 0)
{
lean_object* x_246; 
x_246 = lean_ctor_get(x_242, 1);
lean_inc(x_246);
lean_dec(x_242);
x_213 = x_169;
x_214 = x_246;
goto block_241;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_247 = lean_ctor_get(x_242, 1);
lean_inc(x_247);
lean_dec(x_242);
x_248 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_249 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_248, x_5, x_6, x_7, x_8, x_247);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_unbox(x_250);
lean_dec(x_250);
x_213 = x_252;
x_214 = x_251;
goto block_241;
}
block_212:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_197; 
x_183 = lean_box(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_3);
x_184 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1___boxed), 10, 4);
lean_closure_set(x_184, 0, x_183);
lean_closure_set(x_184, 1, x_3);
lean_closure_set(x_184, 2, x_164);
lean_closure_set(x_184, 3, x_165);
x_197 = lean_nat_dec_lt(x_181, x_3);
lean_dec(x_181);
if (x_197 == 0)
{
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_184);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_198 = lean_box(0);
x_199 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(x_166, x_3, x_164, x_165, x_198, x_5, x_6, x_7, x_8, x_182);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_199;
}
else
{
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_184);
lean_dec(x_180);
lean_dec(x_163);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_200 = lean_box(0);
x_201 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(x_166, x_3, x_164, x_165, x_200, x_5, x_6, x_7, x_8, x_182);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_202 = lean_ctor_get(x_180, 0);
lean_inc(x_202);
lean_dec(x_180);
x_203 = lean_ctor_get(x_162, 0);
lean_inc(x_203);
lean_dec(x_162);
x_204 = lean_name_eq(x_1, x_163);
lean_dec(x_163);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; 
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_184);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_205 = lean_box(0);
x_206 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(x_166, x_3, x_164, x_165, x_205, x_5, x_6, x_7, x_8, x_182);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_206;
}
else
{
uint8_t x_207; 
x_207 = lean_nat_dec_le(x_202, x_203);
lean_dec(x_203);
lean_dec(x_202);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_184);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_208 = lean_box(0);
x_209 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(x_166, x_3, x_164, x_165, x_208, x_5, x_6, x_7, x_8, x_182);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_209;
}
else
{
lean_object* x_210; 
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_3);
x_210 = lean_box(0);
x_185 = x_210;
goto block_196;
}
}
}
}
}
else
{
lean_object* x_211; 
lean_dec(x_180);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_3);
x_211 = lean_box(0);
x_185 = x_211;
goto block_196;
}
block_196:
{
lean_object* x_186; uint8_t x_187; 
lean_dec(x_185);
x_186 = lean_unsigned_to_nat(0u);
x_187 = lean_nat_dec_lt(x_186, x_14);
lean_dec(x_14);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_189 = lean_box(0);
x_190 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3(x_1, x_167, x_184, x_188, x_2, x_189, x_5, x_6, x_7, x_8, x_182);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_191 = l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___rarg(x_6, x_7, x_8, x_182);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_195 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3(x_1, x_167, x_184, x_194, x_2, x_192, x_5, x_6, x_7, x_8, x_193);
lean_dec(x_192);
return x_195;
}
}
}
block_241:
{
if (x_213 == 0)
{
x_182 = x_214;
goto block_212;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_inc(x_3);
x_215 = l_Lean_fmt___at_Lean_Level_LevelToFormat_Result_format___spec__1(x_3);
x_216 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_217 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_218 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_216);
x_219 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__15;
x_220 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
lean_inc(x_181);
x_221 = l_Lean_fmt___at_Lean_Level_LevelToFormat_Result_format___spec__1(x_181);
x_222 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_222, 0, x_221);
x_223 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_222);
x_224 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__16;
x_225 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
lean_inc(x_1);
lean_inc(x_180);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_180);
lean_ctor_set(x_226, 1, x_1);
x_227 = l_Lean_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_226);
x_228 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_228, 0, x_227);
x_229 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_229, 0, x_225);
lean_ctor_set(x_229, 1, x_228);
x_230 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__18;
x_231 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
lean_inc(x_163);
lean_inc(x_162);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_162);
lean_ctor_set(x_232, 1, x_163);
x_233 = l_Lean_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_232);
x_234 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_234, 0, x_233);
x_235 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_235, 0, x_231);
lean_ctor_set(x_235, 1, x_234);
x_236 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_237 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
x_238 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_239 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_238, x_237, x_5, x_6, x_7, x_8, x_214);
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec(x_239);
x_182 = x_240;
goto block_212;
}
}
}
}
block_292:
{
if (x_254 == 0)
{
lean_object* x_256; 
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_256 = lean_apply_5(x_4, x_5, x_6, x_7, x_8, x_255);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
lean_dec(x_256);
x_258 = lean_st_ref_get(x_6, x_257);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_173 = x_259;
x_174 = x_260;
goto block_253;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_261 = lean_ctor_get(x_256, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_256, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_263 = x_256;
} else {
 lean_dec_ref(x_256);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(1, 2, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_261);
lean_ctor_set(x_264, 1, x_262);
return x_264;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_inc(x_163);
lean_inc(x_162);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_162);
lean_ctor_set(x_265, 1, x_163);
x_266 = l_Lean_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_265);
x_267 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_267, 0, x_266);
x_268 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__20;
x_269 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_267);
x_270 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__21;
x_271 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
x_272 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_272, 0, x_11);
x_273 = l_Lean_MessageData_ofList___closed__3;
x_274 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_272);
x_275 = lean_unsigned_to_nat(2u);
x_276 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_274);
x_277 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_277, 0, x_271);
lean_ctor_set(x_277, 1, x_276);
x_278 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_279 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
x_280 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_281 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_280, x_279, x_5, x_6, x_7, x_8, x_255);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
lean_dec(x_281);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_283 = lean_apply_5(x_4, x_5, x_6, x_7, x_8, x_282);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_284 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
lean_dec(x_283);
x_285 = lean_st_ref_get(x_6, x_284);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_173 = x_286;
x_174 = x_287;
goto block_253;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_288 = lean_ctor_get(x_283, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_283, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_290 = x_283;
} else {
 lean_dec_ref(x_283);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(1, 2, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_289);
return x_291;
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
lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_6, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_dec(x_10);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = 1;
lean_ctor_set(x_6, 2, x_12);
lean_ctor_set(x_6, 1, x_11);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_13);
x_14 = lean_st_ref_set(x_1, x_6, x_7);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_1, x_2, x_3, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 3);
x_19 = lean_ctor_get(x_6, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = 1;
x_23 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set(x_23, 3, x_18);
lean_ctor_set(x_23, 4, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*5, x_22);
x_24 = lean_st_ref_set(x_1, x_23, x_7);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_1, x_2, x_3, x_25);
return x_26;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_st_ref_get(x_4, x_7);
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_13);
lean_dec(x_14);
x_25 = lean_st_ref_set(x_4, x_11, x_20);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_dec(x_13);
x_29 = lean_ctor_get(x_14, 0);
lean_inc(x_29);
x_30 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_31 = lean_nat_dec_eq(x_30, x_29);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_14);
x_33 = lean_st_ref_set(x_4, x_11, x_28);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_34);
return x_35;
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
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_throwError___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 3);
x_6 = l_Lean_addMessageContextPartial___at_Lean_Core_Lean_CoreM___instance__6___spec__1(x_1, x_2, x_3, x_4);
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
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_throwError___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_throwError___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_throwError___spec__1___rarg(x_1, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_throwError___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_throwError___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_throwError___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_throwError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_throwError___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextPartial___at_Lean_Core_Lean_CoreM___instance__6___spec__1(x_1, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
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
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no known parenthesizer for kind '");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_12 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_11, x_10, x_1);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___spec__1___rarg(x_17, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_apply_5(x_19, x_2, x_3, x_4, x_5, x_9);
return x_20;
}
}
}
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
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
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_16 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind(x_15, x_3, x_4, x_5, x_6, x_14);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 2);
lean_dec(x_12);
lean_ctor_set(x_9, 2, x_1);
x_13 = lean_st_ref_set(x_4, x_9, x_10);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
x_22 = lean_ctor_get(x_9, 3);
x_23 = lean_ctor_get(x_9, 4);
x_24 = lean_ctor_get_uint8(x_9, sizeof(void*)*5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_25 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_1);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*5, x_24);
x_26 = lean_st_ref_set(x_4, x_25, x_10);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
x_14 = l_System_FilePath_dirName___closed__1;
lean_inc(x_1);
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_1);
x_16 = lean_box(0);
x_17 = 1;
x_18 = lean_box(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed), 8, 3);
lean_closure_set(x_19, 0, x_15);
lean_closure_set(x_19, 1, x_16);
lean_closure_set(x_19, 2, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind), 6, 1);
lean_closure_set(x_20, 0, x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_21 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_19, x_20, x_1, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_1);
x_24 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lambda__1(x_1, x_22, x_1, x_4, x_5, x_6, x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_22);
lean_dec(x_1);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_11);
x_29 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_30 = lean_array_get_size(x_29);
lean_dec(x_29);
lean_inc(x_30);
x_31 = lean_alloc_closure((void*)(l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1___boxed), 7, 2);
lean_closure_set(x_31, 0, x_30);
lean_closure_set(x_31, 1, x_30);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_32 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_31, x_1, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_1);
x_35 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___lambda__1(x_1, x_33, x_1, x_4, x_5, x_6, x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_33);
lean_dec(x_1);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_st_ref_get(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_11, 2);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(x_14);
lean_dec(x_14);
x_16 = lean_nat_sub(x_15, x_1);
lean_dec(x_15);
x_17 = l_Lean_Syntax_getArg(x_13, x_16);
lean_dec(x_16);
lean_dec(x_13);
x_18 = l_Lean_Syntax_getId(x_17);
lean_dec(x_17);
x_19 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_18, x_2, x_3, x_4, x_5, x_6, x_10);
return x_19;
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_3(x_2, x_6, x_3, x_7);
return x_8;
}
}
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = l_Array_empty___closed__1;
x_6 = lean_array_push(x_5, x_1);
x_7 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__5;
x_8 = lean_array_push(x_6, x_7);
x_9 = l_Lean_nullKind___closed__2;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__6;
x_12 = lean_array_push(x_11, x_10);
x_13 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__15;
x_14 = lean_array_push(x_12, x_13);
x_15 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Unhygienic_Lean_Hygiene___instance__1___closed__4;
x_4 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg), 4, 2);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Std_Range___kind_term____x40_Init_Data_Range___hyg_111____closed__17;
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed), 7, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_1);
x_15 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1;
x_16 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_13, x_15, x_1, x_14, x_2, x_3, x_4, x_5, x_9);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg(x_9);
return x_17;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_3 = l_Std_Range___kind_term____x40_Init_Data_Range___hyg_111____closed__17;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer_match__1___rarg), 2, 0);
return x_2;
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
x_1 = l_Lean_mkAppStx___closed__4;
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
x_2 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("seq1");
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_5 = l_Array_empty___closed__1;
x_6 = lean_array_push(x_5, x_1);
x_7 = l_Lean_nullKind___closed__2;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_array_push(x_5, x_8);
x_10 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__5;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__6;
x_13 = lean_array_push(x_12, x_11);
x_14 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__15;
x_15 = lean_array_push(x_13, x_14);
x_16 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__3;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Unhygienic_Lean_Hygiene___instance__1___closed__4;
x_4 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg), 4, 2);
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3;
x_10 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_7, x_9, x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_3 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer_match__1___rarg), 2, 0);
return x_2;
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
x_1 = l_Lean_mkAppStx___closed__4;
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
x_2 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__6;
x_6 = lean_array_push(x_5, x_1);
x_7 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__15;
x_8 = lean_array_push(x_6, x_7);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__3;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Unhygienic_Lean_Hygiene___instance__1___closed__4;
x_4 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg), 4, 2);
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3;
x_10 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_7, x_9, x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_try_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
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
x_46 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_45, x_3, x_4, x_5, x_6, x_44);
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
x_27 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_30 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_29, x_28, x_3, x_4, x_5, x_6, x_14);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(x_2, x_4, x_5, x_6, x_7, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_14, 1);
lean_dec(x_17);
x_18 = l_Lean_Parser_leadPrec___closed__1;
x_19 = l_Nat_min(x_18, x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_14, 1, x_20);
x_21 = lean_st_ref_set(x_5, x_14, x_15);
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 2);
x_30 = lean_ctor_get(x_14, 3);
x_31 = lean_ctor_get(x_14, 4);
x_32 = lean_ctor_get_uint8(x_14, sizeof(void*)*5);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_33 = l_Lean_Parser_leadPrec___closed__1;
x_34 = l_Nat_min(x_33, x_2);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_29);
lean_ctor_set(x_36, 3, x_30);
lean_ctor_set(x_36, 4, x_31);
lean_ctor_set_uint8(x_36, sizeof(void*)*5, x_32);
x_37 = lean_st_ref_set(x_5, x_36, x_15);
lean_dec(x_5);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_9);
if (x_42 == 0)
{
return x_9;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_9, 0);
x_44 = lean_ctor_get(x_9, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_9);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(x_1, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_11, 2);
lean_dec(x_14);
lean_inc(x_3);
lean_ctor_set(x_11, 2, x_3);
x_15 = lean_st_ref_set(x_4, x_11, x_12);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_18 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_3, x_17, x_3, x_4, x_5, x_6, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
x_21 = lean_ctor_get(x_11, 3);
x_22 = lean_ctor_get(x_11, 4);
x_23 = lean_ctor_get_uint8(x_11, sizeof(void*)*5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
lean_inc(x_3);
x_24 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_3);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*5, x_23);
x_25 = lean_st_ref_set(x_4, x_24, x_12);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_28 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_3, x_27, x_3, x_4, x_5, x_6, x_26);
return x_28;
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Syntax_getKind(x_10);
x_13 = lean_name_eq(x_1, x_12);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_st_ref_get(x_7, x_11);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = 0;
x_14 = x_44;
x_15 = x_43;
goto block_38;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_47 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_46, x_4, x_5, x_6, x_7, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_unbox(x_48);
lean_dec(x_48);
x_14 = x_50;
x_15 = x_49;
goto block_38;
}
block_38:
{
if (x_14 == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_16 = l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg(x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_12);
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
x_28 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_31 = l_Lean_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_30, x_29, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_throwBacktrack___rarg(x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_12);
lean_dec(x_1);
x_51 = lean_box(0);
x_52 = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__2(x_2, x_3, x_51, x_4, x_5, x_6, x_7, x_11);
return x_52;
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer___rarg___boxed), 4, 0);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer(x_1, x_2, x_3);
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer(x_1);
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer___rarg___boxed), 4, 0);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer(x_1, x_4, x_3);
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
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_12 = lean_alloc_closure((void*)(l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer___spec__1___boxed), 8, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_11);
x_13 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_12, x_2, x_3, x_4, x_5, x_9);
return x_13;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_many1_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_14 = l_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_9);
return x_14;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_optional_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_List_forM___main___at_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_15 = lean_alloc_closure((void*)(l_List_forM___main___at_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer___spec__1___boxed), 8, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_14);
x_16 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_15, x_3, x_4, x_5, x_6, x_10);
return x_16;
}
}
lean_object* l_List_forM___main___at_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___main___at_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepBy1_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_toggleInsideQuot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
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
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_Syntax_Traverser_left(x_9);
lean_ctor_set(x_6, 0, x_10);
x_11 = lean_st_ref_set(x_1, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get_uint8(x_6, sizeof(void*)*5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_24 = l_Lean_Syntax_Traverser_left(x_18);
x_25 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_25, 4, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*5, x_23);
x_26 = lean_st_ref_set(x_1, x_25, x_7);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___spec__1___rarg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_fget(x_2, x_3);
x_14 = l_Lean_interpolatedStrLitKind;
x_15 = l_Lean_Syntax_isOfKind(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = lean_apply_5(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_3 = x_19;
x_8 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___spec__1___rarg(x_5, x_6, x_7, x_8);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_3, x_27);
lean_dec(x_3);
x_3 = x_28;
x_8 = x_26;
goto _start;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_reverseAux___main___rarg(x_10, x_11);
x_13 = lean_alloc_closure((void*)(l_Array_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___spec__1___boxed), 8, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_11);
x_14 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_13, x_2, x_3, x_4, x_5, x_9);
return x_14;
}
}
lean_object* l_Array_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
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
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesize___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_parenthesize___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_parenthesize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Lean_Syntax_Traverser_fromSyntax(x_2);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = 0;
x_10 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_7);
lean_ctor_set(x_10, 4, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_9);
x_11 = lean_st_mk_ref(x_10, x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_12);
x_14 = lean_apply_5(x_1, x_8, x_12, x_3, x_4, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_12, x_15);
lean_dec(x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_12);
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_14, 0);
lean_dec(x_27);
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_14, 1);
x_32 = lean_ctor_get(x_14, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
x_34 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_35 = lean_nat_dec_eq(x_34, x_33);
lean_dec(x_33);
if (x_35 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_14);
lean_dec(x_25);
x_36 = l_Lean_PrettyPrinter_parenthesize___closed__3;
x_37 = l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_throwError___spec__1___rarg(x_36, x_3, x_4, x_31);
lean_dec(x_4);
lean_dec(x_3);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_dec(x_14);
x_39 = lean_ctor_get(x_25, 0);
lean_inc(x_39);
x_40 = l_Lean_PrettyPrinter_backtrackExceptionId;
x_41 = lean_nat_dec_eq(x_40, x_39);
lean_dec(x_39);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_4);
lean_dec(x_3);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_25);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_25);
x_43 = l_Lean_PrettyPrinter_parenthesize___closed__3;
x_44 = l_Lean_throwError___at_Lean_PrettyPrinter_Parenthesizer_throwError___spec__1___rarg(x_43, x_3, x_4, x_38);
lean_dec(x_4);
lean_dec(x_3);
return x_44;
}
}
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_parenthesizeTerm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range___kind_term____x40_Init_Data_Range___hyg_111____closed__17;
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
x_1 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3123____closed__4;
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
lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_2344_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_CoreM(lean_object*);
lean_object* initialize_Lean_KeyedDeclsAttribute(lean_object*);
lean_object* initialize_Lean_Parser_Extension(lean_object*);
lean_object* initialize_Lean_ParserCompiler_Attribute(lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Backtrack(lean_object*);
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
res = initialize_Lean_PrettyPrinter_Backtrack(lean_io_mk_world());
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
l_Lean_PrettyPrinter_Parenthesizer_State_visitedToken___default = _init_l_Lean_PrettyPrinter_Parenthesizer_State_visitedToken___default();
l_Lean_PrettyPrinter_Lean_PrettyPrinter_Parenthesizer___instance__1___closed__1 = _init_l_Lean_PrettyPrinter_Lean_PrettyPrinter_Parenthesizer___instance__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Lean_PrettyPrinter_Parenthesizer___instance__1___closed__1);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__4 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__4);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__5 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__5);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__6 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__6);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__7 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__7);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__8 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__8);
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
l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__3);
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
l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__5 = _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__5);
l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__6 = _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__6);
l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__7 = _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2___closed__7);
l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__2);
l_Lean_PrettyPrinter_Parenthesizer_visitArgs___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_visitArgs___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_visitArgs___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_Lean_PrettyPrinter_Parenthesizer___instance__3);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__2___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___lambda__3___closed__1);
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
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__17 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__17();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__17);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__18 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__18();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__18);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__19 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__19();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__19);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__20 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__20();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__20);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__21 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__21();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__21);
l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1);
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
l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3);
l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1 = _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1);
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
l_Lean_PrettyPrinter_parenthesize___closed__1 = _init_l_Lean_PrettyPrinter_parenthesize___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesize___closed__1);
l_Lean_PrettyPrinter_parenthesize___closed__2 = _init_l_Lean_PrettyPrinter_parenthesize___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesize___closed__2);
l_Lean_PrettyPrinter_parenthesize___closed__3 = _init_l_Lean_PrettyPrinter_parenthesize___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesize___closed__3);
l_Lean_PrettyPrinter_parenthesizeTerm___closed__1 = _init_l_Lean_PrettyPrinter_parenthesizeTerm___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizeTerm___closed__1);
l_Lean_PrettyPrinter_parenthesizeCommand___closed__1 = _init_l_Lean_PrettyPrinter_parenthesizeCommand___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizeCommand___closed__1);
res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Parenthesizer___hyg_2344_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
