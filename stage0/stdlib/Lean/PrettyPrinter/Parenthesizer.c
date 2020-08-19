// Lean compiler output
// Module: Lean.PrettyPrinter.Parenthesizer
// Imports: Init Lean.Util.ReplaceExpr Lean.Meta.Basic Lean.Meta.WHNF Lean.KeyedDeclsAttribute Lean.Parser.Extension Lean.ParserCompiler
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
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__9;
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14;
lean_object* l_Lean_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__28;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__11;
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1;
extern lean_object* l_Option_HasRepr___rarg___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__1;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_categoryParenthesizerAttribute;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__25;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer(lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__1;
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nullKind;
extern lean_object* l_Lean_mkThunk___closed__1;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__9;
extern lean_object* l_Lean_identKind___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_CombinatorCompilerAttribute_Inhabited___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__17;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___boxed(lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__8;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_EIO_Monad___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__4;
lean_object* l_Lean_Syntax_Traverser_up(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__7;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__10;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__19;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeCommand___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___rarg___closed__1;
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__11;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(lean_object*);
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParser___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__3;
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__7;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__24;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstantUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
extern lean_object* l_Lean_charLitKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__2;
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__4;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__20;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1;
extern lean_object* l_IO_Error_Inhabited;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__15;
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_PrettyPrinter_Parenthesizer_1__regTraceClasses___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__18;
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__7;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_charLitKind___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__2;
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_toggleInsideQuot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__21;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_parenthesizeCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_inhabited;
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__8;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParser___closed__2;
lean_object* l_Lean_PersistentEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeTerm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__13;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__1;
lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer___boxed(lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_monadQuotation___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__11;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer___boxed(lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerCombinatorCompilerAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__17;
lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__3;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant(lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
lean_object* l_EStateM_Inhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1(size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoWs_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__27;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_setCur(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__12;
extern lean_object* l_Lean_Meta_run___rarg___closed__5;
lean_object* l_Lean_CombinatorCompilerAttribute_getDeclFor(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__4;
lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CombinatorCompilerAttribute_setDeclFor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__23;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__7;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
lean_object* l_Lean_PrettyPrinter_parenthesizeCommand___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2;
extern lean_object* l_Lean_Option_format___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__13;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__23;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwOther___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___spec__1(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__1;
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_monadQuotation;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Unhygienic_run___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__12;
extern lean_object* l_Lean_numLitKind___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepBy1_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParserOfStack_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__5;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
extern lean_object* l_Lean_Unhygienic_MonadQuotation___closed__4;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__21;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__21;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParser(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__19;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstantUnsafe___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__4;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesize(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_PrettyPrinter_Parenthesizer_1__regTraceClasses___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Parser_termParser___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_PrettyPrinter_Parenthesizer_1__regTraceClasses___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__22;
extern lean_object* l_Lean_Parser_maxPrec;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__17;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__11;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_monadQuotation___spec__1(lean_object*);
lean_object* l_ReaderT_lift___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getValues___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__1;
extern lean_object* l_Lean_Environment_evalConstCheck___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2;
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_IO_Error_Inhabited___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_IO_ofExcept___at_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_attrParamSyntaxToIdentifier(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__14;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__11;
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___boxed(lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1___closed__2;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__13;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3;
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___boxed(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__16;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__1___closed__2;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__12;
lean_object* l_Lean_KeyedDeclsAttribute_Table_insert___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__3(lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__7;
lean_object* l_StateT_get___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__16(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer(lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__9;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__15;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__4;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__10;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer(lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__14;
lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo___main(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l_StateT_get___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__9;
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__4;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__20;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__22;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Message_toString___spec__1(lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_monadQuotation___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__19;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_down(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1(uint8_t, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_empty___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer(lean_object*);
uint8_t l_Lean_Parser_isParserCategory(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__2(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__18;
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__10;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_right(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_Monad___rarg(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__4;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_add_attribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__3;
lean_object* l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1;
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeCommand___closed__1;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setEnv(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__12;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer___boxed(lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forM___at_IO_runMeta___spec__3(lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
extern lean_object* l_PUnit_Inhabited;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer(lean_object*);
extern lean_object* l_Lean_Option_format___rarg___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__16;
lean_object* l_Lean_Meta_getConstInfo(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_optional_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoWs_parenthesizer(lean_object*);
lean_object* l_Lean_Meta_Exception_toStr(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__29;
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoWs_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__22;
extern lean_object* l_Lean_nameLitKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__4;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___boxed(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
extern lean_object* l_Lean_Format_paren___closed__3;
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3;
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__3;
extern lean_object* l_Lean_MessageData_coeOfOptExpr___closed__1;
extern lean_object* l_Lean_Meta_run___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__1;
lean_object* l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__3;
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__20;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__10;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_lift___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__2(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___closed__1;
lean_object* l_Nat_min(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_many1_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeTerm___closed__1;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_inhabited___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__2;
lean_object* l___private_Lean_PrettyPrinter_Parenthesizer_1__regTraceClasses(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1;
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__4;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__5;
extern lean_object* l_Lean_defaultMaxRecDepth;
lean_object* l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoWs_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__15;
lean_object* l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__18;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParserOfStack_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
lean_object* l_ReaderT_lift___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo___main(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute(lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
lean_object* l_List_forM___main___at_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__16;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Substring_splitOnAux___main___closed__2;
lean_object* l_Lean_SMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__26;
extern lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__24;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_try_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__7;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_initCache;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nameLitKind___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_antiquot_parenthesizer(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer(lean_object*);
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [parenthesizer] argument, expected identifier");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [parenthesizer] argument, unknown syntax kind '");
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_attrParamSyntaxToIdentifier(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2;
return x_5;
}
else
{
if (x_1 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Parser_isValidSyntaxNodeKind(x_2, x_6);
lean_dec(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_Name_toString___closed__1;
x_9 = l_Lean_Name_toStringWithSep___main(x_8, x_6);
x_10 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_6);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
lean_inc(x_16);
lean_inc(x_2);
x_17 = lean_environment_find(x_2, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = l_Lean_Parser_isValidSyntaxNodeKind(x_2, x_16);
lean_dec(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = l_Lean_Name_toString___closed__1;
x_20 = l_Lean_Name_toStringWithSep___main(x_19, x_16);
x_21 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Char_HasRepr___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_16);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_17);
lean_dec(x_2);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_16);
return x_27;
}
}
}
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinParenthesizer");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesizer");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PrettyPrinter");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parenthesizer");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Register a parenthesizer for a parser.\n\n[parenthesizer k] registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` for the `SyntaxNodeKind` `k`.");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__11() {
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
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesizerAttribute");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__13() {
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
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1(x_4, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_mkHashMap___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1___closed__1;
x_3 = l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__3;
x_2 = lean_box(0);
x_3 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_4 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_5 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
x_6 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
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
lean_object* _init_l_Lean_PrettyPrinter_parenthesizerAttribute___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_parenthesizerAttribute___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [parenthesizer] argument, unknown parser category '");
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_attrParamSyntaxToIdentifier(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Parser_isParserCategory(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_Name_toString___closed__1;
x_9 = l_Lean_Name_toStringWithSep___main(x_8, x_6);
x_10 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_6);
return x_15;
}
}
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinCategoryParenthesizer");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("categoryParenthesizer");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CategoryParenthesizer");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_2 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Register a parenthesizer for a syntax category.\n\n[parenthesizer cat] registers a declaration of type `Lean.PrettyPrinter.CategoryParenthesizer` for the category `cat`,\nwhich is used when parenthesizing calls of `categoryParser cat prec`. Implementations should call `maybeParenthesize` with\nthe precedence and an appropriate parentheses builder. If no category parenthesizer is registered, the category will never be\nparenthesized, but still be traversed for parenthesizing nested categories.");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__9() {
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
lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("categoryParenthesizerAttribute");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___closed__11() {
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
lean_object* l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Std_mkHashMap___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_SMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__1___closed__1;
x_3 = l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__1___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_SMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__3;
x_2 = lean_box(0);
x_3 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_4 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_5 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
x_6 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
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
lean_object* _init_l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("combinatorParenthesizer");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Register a parenthesizer for a parser combinator.\n\n[combinatorParenthesizer c] registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` for the `Parser` declaration `c`.\nNote that, unlike with [parenthesizer], this is not a node kind since combinators usually do not introduce their own node kinds.\nThe tagged declaration may optionally accept parameters corresponding to (a prefix of) those of `c`, where `Parser` is replaced\nwith `Parenthesizer` in the parameter types.");
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
x_3 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__3;
x_4 = l_Lean_registerCombinatorCompilerAttribute(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_StateT_get___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_ReaderT_lift___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_ReaderT_lift___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__2___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_apply_1(x_1, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_apply_1(x_1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_21 = x_17;
} else {
 lean_dec_ref(x_17);
 x_21 = lean_box(0);
}
x_22 = lean_apply_1(x_1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__3___rarg), 6, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
lean_ctor_set(x_3, 0, x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*4, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
return x_18;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_apply_1(x_2, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_ctor_set(x_4, 0, x_11);
lean_ctor_set(x_9, 1, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
lean_ctor_set(x_4, 0, x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_ctor_get(x_4, 3);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_22 = lean_apply_1(x_2, x_17);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_19);
lean_ctor_set(x_26, 3, x_20);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_21);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateT_get___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__1;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__2___rarg___boxed), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__3;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__3___rarg), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__2___boxed), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__3___boxed), 6, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__4;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__5;
x_3 = l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__7;
return x_1;
}
}
lean_object* l_StateT_get___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_StateT_get___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_ReaderT_lift___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_ReaderT_lift___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 1);
lean_dec(x_8);
lean_inc(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Nat_min(x_1, x_1);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_3, 2, x_11);
lean_ctor_set(x_3, 1, x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = l_Nat_min(x_16, x_1);
lean_dec(x_1);
lean_dec(x_16);
lean_ctor_set(x_7, 0, x_17);
lean_ctor_set(x_3, 1, x_9);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec(x_7);
x_22 = l_Nat_min(x_21, x_1);
lean_dec(x_1);
lean_dec(x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_3, 2, x_23);
lean_ctor_set(x_3, 1, x_9);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_3, 2);
x_29 = lean_ctor_get(x_3, 3);
x_30 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_3);
lean_inc(x_1);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = l_Nat_min(x_1, x_1);
lean_dec(x_1);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_30);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_5);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_39 = x_28;
} else {
 lean_dec_ref(x_28);
 x_39 = lean_box(0);
}
x_40 = l_Nat_min(x_38, x_1);
lean_dec(x_1);
lean_dec(x_38);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_42, 0, x_27);
lean_ctor_set(x_42, 1, x_31);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_29);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_30);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_5);
return x_45;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Lean_Syntax_Traverser_left(x_5);
lean_ctor_set(x_1, 0, x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_15 = l_Lean_Syntax_Traverser_left(x_10);
x_16 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = l_Lean_Syntax_Traverser_down(x_7, x_1);
lean_ctor_set(x_3, 0, x_8);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_17 = l_Lean_Syntax_Traverser_down(x_12, x_1);
x_18 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*4, x_16);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Lean_Syntax_Traverser_up(x_5);
lean_ctor_set(x_1, 0, x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_15 = l_Lean_Syntax_Traverser_up(x_10);
x_16 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_10, x_4, x_8);
lean_dec(x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_12, x_16);
lean_dec(x_12);
x_18 = l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3(x_17, x_2, x_10, x_4, x_8);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_4);
x_22 = lean_apply_4(x_1, x_2, x_21, x_4, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg(x_25, x_4, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_29, x_4, x_28);
lean_dec(x_4);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_monadQuotation___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_monadQuotation___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_monadQuotation___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_monadQuotation___spec__1___rarg___boxed), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_monadQuotation___spec__1___rarg___boxed), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___lambda__1), 6, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__1;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__2;
x_3 = l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_monadQuotation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__4;
return x_1;
}
}
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_monadQuotation___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_monadQuotation___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(x_5);
lean_dec(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = l_Lean_Syntax_Traverser_setCur(x_7, x_1);
lean_ctor_set(x_3, 0, x_8);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_17 = l_Lean_Syntax_Traverser_setCur(x_12, x_1);
x_18 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*4, x_16);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
}
}
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_Meta_addContext(x_2, x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 4);
lean_inc(x_9);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_8, 4);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_11);
x_18 = l_Std_PersistentArray_push___rarg(x_16, x_17);
lean_ctor_set(x_9, 0, x_18);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
lean_dec(x_9);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_11);
x_24 = l_Std_PersistentArray_push___rarg(x_22, x_23);
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_21);
lean_ctor_set(x_8, 4, x_25);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_7, 0, x_27);
return x_7;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_8, 1);
x_30 = lean_ctor_get(x_8, 2);
x_31 = lean_ctor_get(x_8, 3);
x_32 = lean_ctor_get(x_8, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_8);
x_33 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
x_34 = lean_ctor_get(x_9, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_35 = x_9;
} else {
 lean_dec_ref(x_9);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_11);
x_37 = l_Std_PersistentArray_push___rarg(x_34, x_36);
if (lean_is_scalar(x_35)) {
 x_38 = lean_alloc_ctor(0, 1, 1);
} else {
 x_38 = x_35;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_33);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_29);
lean_ctor_set(x_39, 2, x_30);
lean_ctor_set(x_39, 3, x_31);
lean_ctor_set(x_39, 4, x_38);
lean_ctor_set(x_39, 5, x_32);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_4);
lean_ctor_set(x_7, 1, x_39);
lean_ctor_set(x_7, 0, x_41);
return x_7;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_42 = lean_ctor_get(x_7, 0);
lean_inc(x_42);
lean_dec(x_7);
x_43 = lean_ctor_get(x_8, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_8, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_8, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_8, 5);
lean_inc(x_47);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 lean_ctor_release(x_8, 4);
 lean_ctor_release(x_8, 5);
 x_48 = x_8;
} else {
 lean_dec_ref(x_8);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
x_50 = lean_ctor_get(x_9, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_51 = x_9;
} else {
 lean_dec_ref(x_9);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_42);
x_53 = l_Std_PersistentArray_push___rarg(x_50, x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 1, 1);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_49);
if (lean_is_scalar(x_48)) {
 x_55 = lean_alloc_ctor(0, 6, 0);
} else {
 x_55 = x_48;
}
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_44);
lean_ctor_set(x_55, 2, x_45);
lean_ctor_set(x_55, 3, x_46);
lean_ctor_set(x_55, 4, x_54);
lean_ctor_set(x_55, 5, x_47);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_4);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Lean_Syntax_Traverser_right(x_5);
lean_ctor_set(x_1, 0, x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_15 = l_Lean_Syntax_Traverser_right(x_10);
x_16 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(lean_object* x_1) {
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_3);
x_5 = 0;
x_6 = l_Lean_Option_format___rarg___closed__3;
x_7 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_5);
return x_7;
}
}
}
lean_object* l_Lean_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
x_2 = l_StateT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesize");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__2;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1;
x_2 = l_PUnit_Inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_2 = lean_alloc_closure((void*)(l_ReaderT_inhabited___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.PrettyPrinter.Parenthesizer");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maybeParenthesize: visited a syntax tree without precedences?!");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__7;
x_2 = lean_unsigned_to_nat(198u);
x_3 = lean_unsigned_to_nat(4u);
x_4 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__8;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_maxPrec;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesized: ");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__11;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__12;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Substring_splitOnAux___main___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("...precedences are ");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__15;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__16;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" >? ");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__18;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__19;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" <=? ");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__21;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__22;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesizing (contPrec := ");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__24;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__25;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_paren___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__26;
x_2 = l_Lean_MessageData_coeOfOptExpr___closed__1;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__28;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__27;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg(x_12, x_6, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_1451; lean_object* x_1452; lean_object* x_1493; uint8_t x_1494; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_154 = lean_ctor_get(x_18, 0);
lean_inc(x_154);
x_155 = lean_box(0);
x_156 = 0;
x_157 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
lean_ctor_set(x_157, 2, x_155);
lean_ctor_set(x_157, 3, x_155);
lean_ctor_set_uint8(x_157, sizeof(void*)*4, x_156);
x_1493 = lean_ctor_get(x_15, 4);
lean_inc(x_1493);
x_1494 = lean_ctor_get_uint8(x_1493, sizeof(void*)*1);
lean_dec(x_1493);
if (x_1494 == 0)
{
lean_object* x_1495; 
x_1495 = lean_box(x_156);
lean_ctor_set(x_14, 1, x_157);
lean_ctor_set(x_14, 0, x_1495);
x_1451 = x_14;
x_1452 = x_15;
goto block_1492;
}
else
{
lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; 
x_1496 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1497 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1496, x_6, x_15);
x_1498 = lean_ctor_get(x_1497, 0);
lean_inc(x_1498);
x_1499 = lean_ctor_get(x_1497, 1);
lean_inc(x_1499);
lean_dec(x_1497);
lean_ctor_set(x_14, 1, x_157);
lean_ctor_set(x_14, 0, x_1498);
x_1451 = x_14;
x_1452 = x_1499;
goto block_1492;
}
block_153:
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 1);
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_ctor_get_uint8(x_18, sizeof(void*)*4);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_22, 3);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_22, sizeof(void*)*4);
lean_dec(x_22);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_18, 3);
lean_dec(x_32);
x_33 = lean_ctor_get(x_18, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_18, 0);
lean_dec(x_34);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_18, 3, x_35);
lean_ctor_set(x_18, 1, x_29);
lean_ctor_set(x_18, 0, x_28);
lean_ctor_set_uint8(x_18, sizeof(void*)*4, x_30);
x_36 = lean_box(0);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 0, x_36);
return x_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_18, 2);
lean_inc(x_37);
lean_dec(x_18);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_2);
x_39 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_29);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_39, 3, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_30);
x_40 = lean_box(0);
lean_ctor_set(x_20, 1, x_39);
lean_ctor_set(x_20, 0, x_40);
return x_19;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_dec(x_19);
x_42 = lean_ctor_get(x_22, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_22, 1);
lean_inc(x_43);
x_44 = lean_ctor_get_uint8(x_22, sizeof(void*)*4);
lean_dec(x_22);
x_45 = lean_ctor_get(x_18, 2);
lean_inc(x_45);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 x_46 = x_18;
} else {
 lean_dec_ref(x_18);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_2);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 4, 1);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set(x_48, 2, x_45);
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_44);
x_49 = lean_box(0);
lean_ctor_set(x_20, 1, x_48);
lean_ctor_set(x_20, 0, x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_20);
lean_ctor_set(x_50, 1, x_41);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_19);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_19, 0);
lean_dec(x_52);
x_53 = lean_ctor_get(x_22, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_22, 1);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_22, sizeof(void*)*4);
lean_dec(x_22);
x_56 = !lean_is_exclusive(x_18);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_18, 3);
lean_dec(x_57);
x_58 = lean_ctor_get(x_18, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_18, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_25);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_25, 0);
x_62 = l_Nat_min(x_61, x_2);
lean_dec(x_2);
lean_dec(x_61);
lean_ctor_set(x_25, 0, x_62);
lean_ctor_set(x_18, 3, x_25);
lean_ctor_set(x_18, 1, x_54);
lean_ctor_set(x_18, 0, x_53);
lean_ctor_set_uint8(x_18, sizeof(void*)*4, x_55);
x_63 = lean_box(0);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 0, x_63);
return x_19;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_25, 0);
lean_inc(x_64);
lean_dec(x_25);
x_65 = l_Nat_min(x_64, x_2);
lean_dec(x_2);
lean_dec(x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_18, 3, x_66);
lean_ctor_set(x_18, 1, x_54);
lean_ctor_set(x_18, 0, x_53);
lean_ctor_set_uint8(x_18, sizeof(void*)*4, x_55);
x_67 = lean_box(0);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 0, x_67);
return x_19;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_18, 2);
lean_inc(x_68);
lean_dec(x_18);
x_69 = lean_ctor_get(x_25, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_70 = x_25;
} else {
 lean_dec_ref(x_25);
 x_70 = lean_box(0);
}
x_71 = l_Nat_min(x_69, x_2);
lean_dec(x_2);
lean_dec(x_69);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_73, 0, x_53);
lean_ctor_set(x_73, 1, x_54);
lean_ctor_set(x_73, 2, x_68);
lean_ctor_set(x_73, 3, x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*4, x_55);
x_74 = lean_box(0);
lean_ctor_set(x_20, 1, x_73);
lean_ctor_set(x_20, 0, x_74);
return x_19;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_75 = lean_ctor_get(x_19, 1);
lean_inc(x_75);
lean_dec(x_19);
x_76 = lean_ctor_get(x_22, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_22, 1);
lean_inc(x_77);
x_78 = lean_ctor_get_uint8(x_22, sizeof(void*)*4);
lean_dec(x_22);
x_79 = lean_ctor_get(x_18, 2);
lean_inc(x_79);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 x_80 = x_18;
} else {
 lean_dec_ref(x_18);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_25, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_82 = x_25;
} else {
 lean_dec_ref(x_25);
 x_82 = lean_box(0);
}
x_83 = l_Nat_min(x_81, x_2);
lean_dec(x_2);
lean_dec(x_81);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 4, 1);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_76);
lean_ctor_set(x_85, 1, x_77);
lean_ctor_set(x_85, 2, x_79);
lean_ctor_set(x_85, 3, x_84);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_78);
x_86 = lean_box(0);
lean_ctor_set(x_20, 1, x_85);
lean_ctor_set(x_20, 0, x_86);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_20);
lean_ctor_set(x_87, 1, x_75);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_19);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_19, 0);
lean_dec(x_89);
x_90 = lean_ctor_get(x_22, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_22, 1);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_22, sizeof(void*)*4);
lean_dec(x_22);
x_93 = !lean_is_exclusive(x_18);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_18, 1);
lean_dec(x_94);
x_95 = lean_ctor_get(x_18, 0);
lean_dec(x_95);
lean_ctor_set(x_18, 1, x_91);
lean_ctor_set(x_18, 0, x_90);
lean_ctor_set_uint8(x_18, sizeof(void*)*4, x_92);
x_96 = lean_box(0);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 0, x_96);
return x_19;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_18, 2);
x_98 = lean_ctor_get(x_18, 3);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_18);
x_99 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_99, 0, x_90);
lean_ctor_set(x_99, 1, x_91);
lean_ctor_set(x_99, 2, x_97);
lean_ctor_set(x_99, 3, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*4, x_92);
x_100 = lean_box(0);
lean_ctor_set(x_20, 1, x_99);
lean_ctor_set(x_20, 0, x_100);
return x_19;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_101 = lean_ctor_get(x_19, 1);
lean_inc(x_101);
lean_dec(x_19);
x_102 = lean_ctor_get(x_22, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_22, 1);
lean_inc(x_103);
x_104 = lean_ctor_get_uint8(x_22, sizeof(void*)*4);
lean_dec(x_22);
x_105 = lean_ctor_get(x_18, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_18, 3);
lean_inc(x_106);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 x_107 = x_18;
} else {
 lean_dec_ref(x_18);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 4, 1);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_102);
lean_ctor_set(x_108, 1, x_103);
lean_ctor_set(x_108, 2, x_105);
lean_ctor_set(x_108, 3, x_106);
lean_ctor_set_uint8(x_108, sizeof(void*)*4, x_104);
x_109 = lean_box(0);
lean_ctor_set(x_20, 1, x_108);
lean_ctor_set(x_20, 0, x_109);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_20);
lean_ctor_set(x_110, 1, x_101);
return x_110;
}
}
}
else
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_20, 1);
lean_inc(x_111);
lean_dec(x_20);
x_112 = lean_ctor_get_uint8(x_18, sizeof(void*)*4);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_111, 3);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_114 = lean_ctor_get(x_19, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_115 = x_19;
} else {
 lean_dec_ref(x_19);
 x_115 = lean_box(0);
}
x_116 = lean_ctor_get(x_111, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_111, 1);
lean_inc(x_117);
x_118 = lean_ctor_get_uint8(x_111, sizeof(void*)*4);
lean_dec(x_111);
x_119 = lean_ctor_get(x_18, 2);
lean_inc(x_119);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 x_120 = x_18;
} else {
 lean_dec_ref(x_18);
 x_120 = lean_box(0);
}
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_2);
if (lean_is_scalar(x_120)) {
 x_122 = lean_alloc_ctor(0, 4, 1);
} else {
 x_122 = x_120;
}
lean_ctor_set(x_122, 0, x_116);
lean_ctor_set(x_122, 1, x_117);
lean_ctor_set(x_122, 2, x_119);
lean_ctor_set(x_122, 3, x_121);
lean_ctor_set_uint8(x_122, sizeof(void*)*4, x_118);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
if (lean_is_scalar(x_115)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_115;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_114);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_126 = lean_ctor_get(x_19, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_127 = x_19;
} else {
 lean_dec_ref(x_19);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_111, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_111, 1);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_111, sizeof(void*)*4);
lean_dec(x_111);
x_131 = lean_ctor_get(x_18, 2);
lean_inc(x_131);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 x_132 = x_18;
} else {
 lean_dec_ref(x_18);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_113, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_134 = x_113;
} else {
 lean_dec_ref(x_113);
 x_134 = lean_box(0);
}
x_135 = l_Nat_min(x_133, x_2);
lean_dec(x_2);
lean_dec(x_133);
if (lean_is_scalar(x_134)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_134;
}
lean_ctor_set(x_136, 0, x_135);
if (lean_is_scalar(x_132)) {
 x_137 = lean_alloc_ctor(0, 4, 1);
} else {
 x_137 = x_132;
}
lean_ctor_set(x_137, 0, x_128);
lean_ctor_set(x_137, 1, x_129);
lean_ctor_set(x_137, 2, x_131);
lean_ctor_set(x_137, 3, x_136);
lean_ctor_set_uint8(x_137, sizeof(void*)*4, x_130);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
if (lean_is_scalar(x_127)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_127;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_126);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_2);
x_141 = lean_ctor_get(x_19, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_142 = x_19;
} else {
 lean_dec_ref(x_19);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_111, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_111, 1);
lean_inc(x_144);
x_145 = lean_ctor_get_uint8(x_111, sizeof(void*)*4);
lean_dec(x_111);
x_146 = lean_ctor_get(x_18, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_18, 3);
lean_inc(x_147);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 x_148 = x_18;
} else {
 lean_dec_ref(x_18);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(0, 4, 1);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_143);
lean_ctor_set(x_149, 1, x_144);
lean_ctor_set(x_149, 2, x_146);
lean_ctor_set(x_149, 3, x_147);
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_145);
x_150 = lean_box(0);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_149);
if (lean_is_scalar(x_142)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_142;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_141);
return x_152;
}
}
}
block_1450:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
lean_inc(x_1);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_1);
lean_inc(x_6);
x_162 = lean_apply_4(x_3, x_161, x_160, x_6, x_159);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_163, 1);
x_166 = lean_ctor_get(x_163, 0);
lean_dec(x_166);
x_167 = lean_ctor_get(x_165, 2);
lean_inc(x_167);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_free_object(x_163);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_168 = lean_ctor_get(x_162, 1);
lean_inc(x_168);
lean_dec(x_162);
x_169 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6;
x_170 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__9;
x_171 = lean_panic_fn(x_169, x_170);
x_172 = lean_apply_4(x_171, x_4, x_165, x_6, x_168);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_1057; lean_object* x_1058; lean_object* x_1093; uint8_t x_1094; 
x_173 = lean_ctor_get(x_162, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_174 = x_162;
} else {
 lean_dec_ref(x_162);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_165, 3);
lean_inc(x_175);
x_176 = lean_ctor_get(x_167, 0);
lean_inc(x_176);
lean_dec(x_167);
x_1093 = lean_ctor_get(x_173, 4);
lean_inc(x_1093);
x_1094 = lean_ctor_get_uint8(x_1093, sizeof(void*)*1);
lean_dec(x_1093);
if (x_1094 == 0)
{
lean_object* x_1095; 
x_1095 = lean_box(x_156);
lean_ctor_set(x_163, 0, x_1095);
x_1057 = x_163;
x_1058 = x_173;
goto block_1092;
}
else
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; 
x_1096 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1097 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1096, x_6, x_173);
x_1098 = lean_ctor_get(x_1097, 0);
lean_inc(x_1098);
x_1099 = lean_ctor_get(x_1097, 1);
lean_inc(x_1099);
lean_dec(x_1097);
lean_ctor_set(x_163, 0, x_1098);
x_1057 = x_163;
x_1058 = x_1099;
goto block_1092;
}
block_1056:
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_177);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_225; uint8_t x_755; 
x_180 = lean_ctor_get(x_177, 1);
x_181 = lean_ctor_get(x_177, 0);
lean_dec(x_181);
x_755 = lean_nat_dec_lt(x_176, x_2);
lean_dec(x_176);
if (x_755 == 0)
{
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_756; lean_object* x_757; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_756 = lean_box(0);
lean_ctor_set(x_177, 0, x_756);
if (lean_is_scalar(x_174)) {
 x_757 = lean_alloc_ctor(0, 2, 0);
} else {
 x_757 = x_174;
}
lean_ctor_set(x_757, 0, x_177);
lean_ctor_set(x_757, 1, x_178);
x_19 = x_757;
goto block_153;
}
else
{
lean_object* x_758; 
x_758 = lean_ctor_get(x_18, 1);
lean_inc(x_758);
if (lean_obj_tag(x_758) == 0)
{
lean_object* x_759; lean_object* x_760; 
lean_dec(x_175);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_759 = lean_box(0);
lean_ctor_set(x_177, 0, x_759);
if (lean_is_scalar(x_174)) {
 x_760 = lean_alloc_ctor(0, 2, 0);
} else {
 x_760 = x_174;
}
lean_ctor_set(x_760, 0, x_177);
lean_ctor_set(x_760, 1, x_178);
x_19 = x_760;
goto block_153;
}
else
{
lean_object* x_761; lean_object* x_762; uint8_t x_763; 
x_761 = lean_ctor_get(x_175, 0);
lean_inc(x_761);
lean_dec(x_175);
x_762 = lean_ctor_get(x_758, 0);
lean_inc(x_762);
lean_dec(x_758);
x_763 = lean_nat_dec_le(x_761, x_762);
lean_dec(x_762);
lean_dec(x_761);
if (x_763 == 0)
{
lean_object* x_764; lean_object* x_765; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_764 = lean_box(0);
lean_ctor_set(x_177, 0, x_764);
if (lean_is_scalar(x_174)) {
 x_765 = lean_alloc_ctor(0, 2, 0);
} else {
 x_765 = x_174;
}
lean_ctor_set(x_765, 0, x_177);
lean_ctor_set(x_765, 1, x_178);
x_19 = x_765;
goto block_153;
}
else
{
lean_object* x_766; 
lean_free_object(x_177);
lean_dec(x_174);
x_766 = lean_box(0);
x_225 = x_766;
goto block_754;
}
}
}
}
else
{
lean_object* x_767; 
lean_free_object(x_177);
lean_dec(x_175);
lean_dec(x_174);
x_767 = lean_box(0);
x_225 = x_767;
goto block_754;
}
block_224:
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_184, x_6, x_183);
lean_dec(x_6);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_188 = lean_ctor_get(x_186, 1);
x_189 = lean_ctor_get(x_186, 0);
lean_dec(x_189);
x_190 = !lean_is_exclusive(x_185);
if (x_190 == 0)
{
lean_object* x_191; uint8_t x_192; 
x_191 = lean_ctor_get(x_185, 0);
lean_dec(x_191);
x_192 = !lean_is_exclusive(x_188);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_188, 3);
lean_dec(x_193);
x_194 = lean_ctor_get(x_188, 1);
lean_dec(x_194);
x_195 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
lean_ctor_set(x_188, 3, x_155);
lean_ctor_set(x_188, 1, x_195);
x_196 = lean_box(0);
lean_ctor_set(x_186, 0, x_196);
x_19 = x_185;
goto block_153;
}
else
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_197 = lean_ctor_get(x_188, 0);
x_198 = lean_ctor_get(x_188, 2);
x_199 = lean_ctor_get_uint8(x_188, sizeof(void*)*4);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_188);
x_200 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
x_201 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_201, 0, x_197);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set(x_201, 2, x_198);
lean_ctor_set(x_201, 3, x_155);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_199);
x_202 = lean_box(0);
lean_ctor_set(x_186, 1, x_201);
lean_ctor_set(x_186, 0, x_202);
x_19 = x_185;
goto block_153;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_203 = lean_ctor_get(x_185, 1);
lean_inc(x_203);
lean_dec(x_185);
x_204 = lean_ctor_get(x_188, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_188, 2);
lean_inc(x_205);
x_206 = lean_ctor_get_uint8(x_188, sizeof(void*)*4);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_207 = x_188;
} else {
 lean_dec_ref(x_188);
 x_207 = lean_box(0);
}
x_208 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
if (lean_is_scalar(x_207)) {
 x_209 = lean_alloc_ctor(0, 4, 1);
} else {
 x_209 = x_207;
}
lean_ctor_set(x_209, 0, x_204);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set(x_209, 2, x_205);
lean_ctor_set(x_209, 3, x_155);
lean_ctor_set_uint8(x_209, sizeof(void*)*4, x_206);
x_210 = lean_box(0);
lean_ctor_set(x_186, 1, x_209);
lean_ctor_set(x_186, 0, x_210);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_186);
lean_ctor_set(x_211, 1, x_203);
x_19 = x_211;
goto block_153;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_212 = lean_ctor_get(x_186, 1);
lean_inc(x_212);
lean_dec(x_186);
x_213 = lean_ctor_get(x_185, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_214 = x_185;
} else {
 lean_dec_ref(x_185);
 x_214 = lean_box(0);
}
x_215 = lean_ctor_get(x_212, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_212, 2);
lean_inc(x_216);
x_217 = lean_ctor_get_uint8(x_212, sizeof(void*)*4);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 lean_ctor_release(x_212, 2);
 lean_ctor_release(x_212, 3);
 x_218 = x_212;
} else {
 lean_dec_ref(x_212);
 x_218 = lean_box(0);
}
x_219 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
if (lean_is_scalar(x_218)) {
 x_220 = lean_alloc_ctor(0, 4, 1);
} else {
 x_220 = x_218;
}
lean_ctor_set(x_220, 0, x_215);
lean_ctor_set(x_220, 1, x_219);
lean_ctor_set(x_220, 2, x_216);
lean_ctor_set(x_220, 3, x_155);
lean_ctor_set_uint8(x_220, sizeof(void*)*4, x_217);
x_221 = lean_box(0);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_220);
if (lean_is_scalar(x_214)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_214;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_213);
x_19 = x_223;
goto block_153;
}
}
block_754:
{
lean_object* x_226; uint8_t x_227; 
lean_dec(x_225);
x_226 = lean_unsigned_to_nat(0u);
x_227 = lean_nat_dec_lt(x_226, x_17);
lean_dec(x_17);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_228 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_180, x_6, x_178);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = lean_ctor_get(x_229, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
lean_dec(x_229);
x_233 = l_Lean_Syntax_getHeadInfo___main(x_231);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_234 = lean_apply_1(x_1, x_231);
x_235 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_234, x_4, x_232, x_6, x_230);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_238, x_6, x_237);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_242 = lean_ctor_get(x_241, 4);
lean_inc(x_242);
x_243 = lean_ctor_get_uint8(x_242, sizeof(void*)*1);
lean_dec(x_242);
if (x_243 == 0)
{
uint8_t x_244; 
lean_dec(x_4);
x_244 = !lean_is_exclusive(x_240);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_240, 0);
lean_dec(x_245);
x_246 = lean_box(0);
lean_ctor_set(x_240, 0, x_246);
x_182 = x_240;
x_183 = x_241;
goto block_224;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_240, 1);
lean_inc(x_247);
lean_dec(x_240);
x_248 = lean_box(0);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
x_182 = x_249;
x_183 = x_241;
goto block_224;
}
}
else
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_240);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_251 = lean_ctor_get(x_240, 0);
x_252 = lean_ctor_get(x_240, 1);
x_253 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_254 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_253, x_6, x_241);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_unbox(x_255);
lean_dec(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_251);
lean_dec(x_4);
x_257 = lean_ctor_get(x_254, 1);
lean_inc(x_257);
lean_dec(x_254);
x_258 = lean_box(0);
lean_ctor_set(x_240, 0, x_258);
x_182 = x_240;
x_183 = x_257;
goto block_224;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_free_object(x_240);
x_259 = lean_ctor_get(x_254, 1);
lean_inc(x_259);
lean_dec(x_254);
x_260 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_226, x_251);
x_261 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_261, 0, x_260);
x_262 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_263 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_261);
x_264 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_253, x_263, x_4, x_252, x_6, x_259);
lean_dec(x_4);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_182 = x_265;
x_183 = x_266;
goto block_224;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_267 = lean_ctor_get(x_240, 0);
x_268 = lean_ctor_get(x_240, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_240);
x_269 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_270 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_269, x_6, x_241);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_unbox(x_271);
lean_dec(x_271);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_267);
lean_dec(x_4);
x_273 = lean_ctor_get(x_270, 1);
lean_inc(x_273);
lean_dec(x_270);
x_274 = lean_box(0);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_268);
x_182 = x_275;
x_183 = x_273;
goto block_224;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_276 = lean_ctor_get(x_270, 1);
lean_inc(x_276);
lean_dec(x_270);
x_277 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_226, x_267);
x_278 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_278, 0, x_277);
x_279 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_280 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_278);
x_281 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_269, x_280, x_4, x_268, x_6, x_276);
lean_dec(x_4);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_182 = x_282;
x_183 = x_283;
goto block_224;
}
}
}
}
else
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_233, 0);
lean_inc(x_284);
lean_dec(x_233);
x_285 = l_Lean_Syntax_getTailInfo___main(x_231);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
lean_dec(x_284);
x_286 = lean_apply_1(x_1, x_231);
x_287 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_286, x_4, x_232, x_6, x_230);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
x_291 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_290, x_6, x_289);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
x_294 = lean_ctor_get(x_293, 4);
lean_inc(x_294);
x_295 = lean_ctor_get_uint8(x_294, sizeof(void*)*1);
lean_dec(x_294);
if (x_295 == 0)
{
uint8_t x_296; 
lean_dec(x_4);
x_296 = !lean_is_exclusive(x_292);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_292, 0);
lean_dec(x_297);
x_298 = lean_box(0);
lean_ctor_set(x_292, 0, x_298);
x_182 = x_292;
x_183 = x_293;
goto block_224;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_292, 1);
lean_inc(x_299);
lean_dec(x_292);
x_300 = lean_box(0);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_299);
x_182 = x_301;
x_183 = x_293;
goto block_224;
}
}
else
{
uint8_t x_302; 
x_302 = !lean_is_exclusive(x_292);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_303 = lean_ctor_get(x_292, 0);
x_304 = lean_ctor_get(x_292, 1);
x_305 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_306 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_305, x_6, x_293);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_unbox(x_307);
lean_dec(x_307);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; 
lean_dec(x_303);
lean_dec(x_4);
x_309 = lean_ctor_get(x_306, 1);
lean_inc(x_309);
lean_dec(x_306);
x_310 = lean_box(0);
lean_ctor_set(x_292, 0, x_310);
x_182 = x_292;
x_183 = x_309;
goto block_224;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_free_object(x_292);
x_311 = lean_ctor_get(x_306, 1);
lean_inc(x_311);
lean_dec(x_306);
x_312 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_226, x_303);
x_313 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_313, 0, x_312);
x_314 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_315 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_313);
x_316 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_305, x_315, x_4, x_304, x_6, x_311);
lean_dec(x_4);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_182 = x_317;
x_183 = x_318;
goto block_224;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_319 = lean_ctor_get(x_292, 0);
x_320 = lean_ctor_get(x_292, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_292);
x_321 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_322 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_321, x_6, x_293);
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_unbox(x_323);
lean_dec(x_323);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_319);
lean_dec(x_4);
x_325 = lean_ctor_get(x_322, 1);
lean_inc(x_325);
lean_dec(x_322);
x_326 = lean_box(0);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_320);
x_182 = x_327;
x_183 = x_325;
goto block_224;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_328 = lean_ctor_get(x_322, 1);
lean_inc(x_328);
lean_dec(x_322);
x_329 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_226, x_319);
x_330 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_330, 0, x_329);
x_331 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_332 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_330);
x_333 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_321, x_332, x_4, x_320, x_6, x_328);
lean_dec(x_4);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
lean_dec(x_333);
x_182 = x_334;
x_183 = x_335;
goto block_224;
}
}
}
}
else
{
lean_object* x_336; uint8_t x_337; 
x_336 = lean_ctor_get(x_285, 0);
lean_inc(x_336);
lean_dec(x_285);
x_337 = !lean_is_exclusive(x_284);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; 
x_338 = lean_ctor_get(x_284, 0);
x_339 = lean_ctor_get(x_284, 1);
x_340 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14;
lean_inc(x_339);
lean_ctor_set(x_284, 0, x_340);
x_341 = l_Lean_Syntax_setHeadInfo(x_231, x_284);
x_342 = !lean_is_exclusive(x_336);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; 
x_343 = lean_ctor_get(x_336, 1);
x_344 = lean_ctor_get(x_336, 2);
lean_inc(x_343);
lean_ctor_set(x_336, 2, x_340);
x_345 = l_Lean_Syntax_setTailInfo(x_341, x_336);
x_346 = lean_apply_1(x_1, x_345);
x_347 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_347, 0, x_338);
lean_ctor_set(x_347, 1, x_339);
lean_ctor_set(x_347, 2, x_340);
x_348 = l_Lean_Syntax_setHeadInfo(x_346, x_347);
x_349 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_349, 0, x_340);
lean_ctor_set(x_349, 1, x_343);
lean_ctor_set(x_349, 2, x_344);
x_350 = l_Lean_Syntax_setTailInfo(x_348, x_349);
x_351 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_350, x_4, x_232, x_6, x_230);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
x_355 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_354, x_6, x_353);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
x_358 = lean_ctor_get(x_357, 4);
lean_inc(x_358);
x_359 = lean_ctor_get_uint8(x_358, sizeof(void*)*1);
lean_dec(x_358);
if (x_359 == 0)
{
uint8_t x_360; 
lean_dec(x_4);
x_360 = !lean_is_exclusive(x_356);
if (x_360 == 0)
{
lean_object* x_361; lean_object* x_362; 
x_361 = lean_ctor_get(x_356, 0);
lean_dec(x_361);
x_362 = lean_box(0);
lean_ctor_set(x_356, 0, x_362);
x_182 = x_356;
x_183 = x_357;
goto block_224;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_363 = lean_ctor_get(x_356, 1);
lean_inc(x_363);
lean_dec(x_356);
x_364 = lean_box(0);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_363);
x_182 = x_365;
x_183 = x_357;
goto block_224;
}
}
else
{
uint8_t x_366; 
x_366 = !lean_is_exclusive(x_356);
if (x_366 == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; 
x_367 = lean_ctor_get(x_356, 0);
x_368 = lean_ctor_get(x_356, 1);
x_369 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_370 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_369, x_6, x_357);
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_unbox(x_371);
lean_dec(x_371);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; 
lean_dec(x_367);
lean_dec(x_4);
x_373 = lean_ctor_get(x_370, 1);
lean_inc(x_373);
lean_dec(x_370);
x_374 = lean_box(0);
lean_ctor_set(x_356, 0, x_374);
x_182 = x_356;
x_183 = x_373;
goto block_224;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_free_object(x_356);
x_375 = lean_ctor_get(x_370, 1);
lean_inc(x_375);
lean_dec(x_370);
x_376 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_226, x_367);
x_377 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_377, 0, x_376);
x_378 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_379 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_377);
x_380 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_369, x_379, x_4, x_368, x_6, x_375);
lean_dec(x_4);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
x_182 = x_381;
x_183 = x_382;
goto block_224;
}
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; 
x_383 = lean_ctor_get(x_356, 0);
x_384 = lean_ctor_get(x_356, 1);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_356);
x_385 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_386 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_385, x_6, x_357);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_unbox(x_387);
lean_dec(x_387);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_383);
lean_dec(x_4);
x_389 = lean_ctor_get(x_386, 1);
lean_inc(x_389);
lean_dec(x_386);
x_390 = lean_box(0);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_384);
x_182 = x_391;
x_183 = x_389;
goto block_224;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_392 = lean_ctor_get(x_386, 1);
lean_inc(x_392);
lean_dec(x_386);
x_393 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_226, x_383);
x_394 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_394, 0, x_393);
x_395 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_396 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_394);
x_397 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_385, x_396, x_4, x_384, x_6, x_392);
lean_dec(x_4);
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
lean_dec(x_397);
x_182 = x_398;
x_183 = x_399;
goto block_224;
}
}
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
x_400 = lean_ctor_get(x_336, 0);
x_401 = lean_ctor_get(x_336, 1);
x_402 = lean_ctor_get(x_336, 2);
lean_inc(x_402);
lean_inc(x_401);
lean_inc(x_400);
lean_dec(x_336);
lean_inc(x_401);
x_403 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_403, 0, x_400);
lean_ctor_set(x_403, 1, x_401);
lean_ctor_set(x_403, 2, x_340);
x_404 = l_Lean_Syntax_setTailInfo(x_341, x_403);
x_405 = lean_apply_1(x_1, x_404);
x_406 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_406, 0, x_338);
lean_ctor_set(x_406, 1, x_339);
lean_ctor_set(x_406, 2, x_340);
x_407 = l_Lean_Syntax_setHeadInfo(x_405, x_406);
x_408 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_408, 0, x_340);
lean_ctor_set(x_408, 1, x_401);
lean_ctor_set(x_408, 2, x_402);
x_409 = l_Lean_Syntax_setTailInfo(x_407, x_408);
x_410 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_409, x_4, x_232, x_6, x_230);
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
lean_dec(x_410);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_413, x_6, x_412);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
x_417 = lean_ctor_get(x_416, 4);
lean_inc(x_417);
x_418 = lean_ctor_get_uint8(x_417, sizeof(void*)*1);
lean_dec(x_417);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_4);
x_419 = lean_ctor_get(x_415, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_420 = x_415;
} else {
 lean_dec_ref(x_415);
 x_420 = lean_box(0);
}
x_421 = lean_box(0);
if (lean_is_scalar(x_420)) {
 x_422 = lean_alloc_ctor(0, 2, 0);
} else {
 x_422 = x_420;
}
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_419);
x_182 = x_422;
x_183 = x_416;
goto block_224;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; 
x_423 = lean_ctor_get(x_415, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_415, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_425 = x_415;
} else {
 lean_dec_ref(x_415);
 x_425 = lean_box(0);
}
x_426 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_427 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_426, x_6, x_416);
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_unbox(x_428);
lean_dec(x_428);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_423);
lean_dec(x_4);
x_430 = lean_ctor_get(x_427, 1);
lean_inc(x_430);
lean_dec(x_427);
x_431 = lean_box(0);
if (lean_is_scalar(x_425)) {
 x_432 = lean_alloc_ctor(0, 2, 0);
} else {
 x_432 = x_425;
}
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_424);
x_182 = x_432;
x_183 = x_430;
goto block_224;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_dec(x_425);
x_433 = lean_ctor_get(x_427, 1);
lean_inc(x_433);
lean_dec(x_427);
x_434 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_226, x_423);
x_435 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_435, 0, x_434);
x_436 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_437 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_435);
x_438 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_426, x_437, x_4, x_424, x_6, x_433);
lean_dec(x_4);
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
lean_dec(x_438);
x_182 = x_439;
x_183 = x_440;
goto block_224;
}
}
}
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; 
x_441 = lean_ctor_get(x_284, 0);
x_442 = lean_ctor_get(x_284, 1);
x_443 = lean_ctor_get(x_284, 2);
lean_inc(x_443);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_284);
x_444 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14;
lean_inc(x_442);
x_445 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_442);
lean_ctor_set(x_445, 2, x_443);
x_446 = l_Lean_Syntax_setHeadInfo(x_231, x_445);
x_447 = lean_ctor_get(x_336, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_336, 1);
lean_inc(x_448);
x_449 = lean_ctor_get(x_336, 2);
lean_inc(x_449);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 x_450 = x_336;
} else {
 lean_dec_ref(x_336);
 x_450 = lean_box(0);
}
lean_inc(x_448);
if (lean_is_scalar(x_450)) {
 x_451 = lean_alloc_ctor(0, 3, 0);
} else {
 x_451 = x_450;
}
lean_ctor_set(x_451, 0, x_447);
lean_ctor_set(x_451, 1, x_448);
lean_ctor_set(x_451, 2, x_444);
x_452 = l_Lean_Syntax_setTailInfo(x_446, x_451);
x_453 = lean_apply_1(x_1, x_452);
x_454 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_454, 0, x_441);
lean_ctor_set(x_454, 1, x_442);
lean_ctor_set(x_454, 2, x_444);
x_455 = l_Lean_Syntax_setHeadInfo(x_453, x_454);
x_456 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_456, 0, x_444);
lean_ctor_set(x_456, 1, x_448);
lean_ctor_set(x_456, 2, x_449);
x_457 = l_Lean_Syntax_setTailInfo(x_455, x_456);
x_458 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_457, x_4, x_232, x_6, x_230);
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
lean_dec(x_458);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
lean_dec(x_459);
x_462 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_461, x_6, x_460);
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec(x_462);
x_465 = lean_ctor_get(x_464, 4);
lean_inc(x_465);
x_466 = lean_ctor_get_uint8(x_465, sizeof(void*)*1);
lean_dec(x_465);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
lean_dec(x_4);
x_467 = lean_ctor_get(x_463, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_468 = x_463;
} else {
 lean_dec_ref(x_463);
 x_468 = lean_box(0);
}
x_469 = lean_box(0);
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(0, 2, 0);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set(x_470, 1, x_467);
x_182 = x_470;
x_183 = x_464;
goto block_224;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_477; 
x_471 = lean_ctor_get(x_463, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_463, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_473 = x_463;
} else {
 lean_dec_ref(x_463);
 x_473 = lean_box(0);
}
x_474 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_475 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_474, x_6, x_464);
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_unbox(x_476);
lean_dec(x_476);
if (x_477 == 0)
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; 
lean_dec(x_471);
lean_dec(x_4);
x_478 = lean_ctor_get(x_475, 1);
lean_inc(x_478);
lean_dec(x_475);
x_479 = lean_box(0);
if (lean_is_scalar(x_473)) {
 x_480 = lean_alloc_ctor(0, 2, 0);
} else {
 x_480 = x_473;
}
lean_ctor_set(x_480, 0, x_479);
lean_ctor_set(x_480, 1, x_472);
x_182 = x_480;
x_183 = x_478;
goto block_224;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_473);
x_481 = lean_ctor_get(x_475, 1);
lean_inc(x_481);
lean_dec(x_475);
x_482 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_226, x_471);
x_483 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_483, 0, x_482);
x_484 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_485 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_483);
x_486 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_474, x_485, x_4, x_472, x_6, x_481);
lean_dec(x_4);
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_486, 1);
lean_inc(x_488);
lean_dec(x_486);
x_182 = x_487;
x_183 = x_488;
goto block_224;
}
}
}
}
}
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_489 = l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___rarg(x_180, x_6, x_178);
x_490 = lean_ctor_get(x_489, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_489, 1);
lean_inc(x_491);
lean_dec(x_489);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
lean_dec(x_490);
x_493 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_492, x_6, x_491);
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_493, 1);
lean_inc(x_495);
lean_dec(x_493);
x_496 = lean_ctor_get(x_494, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_494, 1);
lean_inc(x_497);
lean_dec(x_494);
x_498 = l_Lean_Syntax_getHeadInfo___main(x_496);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; uint8_t x_508; 
x_499 = lean_apply_1(x_1, x_496);
x_500 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_499, x_4, x_497, x_6, x_495);
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
x_503 = lean_ctor_get(x_501, 1);
lean_inc(x_503);
lean_dec(x_501);
x_504 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_503, x_6, x_502);
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_504, 1);
lean_inc(x_506);
lean_dec(x_504);
x_507 = lean_ctor_get(x_506, 4);
lean_inc(x_507);
x_508 = lean_ctor_get_uint8(x_507, sizeof(void*)*1);
lean_dec(x_507);
if (x_508 == 0)
{
uint8_t x_509; 
lean_dec(x_4);
x_509 = !lean_is_exclusive(x_505);
if (x_509 == 0)
{
lean_object* x_510; lean_object* x_511; 
x_510 = lean_ctor_get(x_505, 0);
lean_dec(x_510);
x_511 = lean_box(0);
lean_ctor_set(x_505, 0, x_511);
x_182 = x_505;
x_183 = x_506;
goto block_224;
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_512 = lean_ctor_get(x_505, 1);
lean_inc(x_512);
lean_dec(x_505);
x_513 = lean_box(0);
x_514 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_514, 0, x_513);
lean_ctor_set(x_514, 1, x_512);
x_182 = x_514;
x_183 = x_506;
goto block_224;
}
}
else
{
uint8_t x_515; 
x_515 = !lean_is_exclusive(x_505);
if (x_515 == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; uint8_t x_521; 
x_516 = lean_ctor_get(x_505, 0);
x_517 = lean_ctor_get(x_505, 1);
x_518 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_519 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_518, x_6, x_506);
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_unbox(x_520);
lean_dec(x_520);
if (x_521 == 0)
{
lean_object* x_522; lean_object* x_523; 
lean_dec(x_516);
lean_dec(x_4);
x_522 = lean_ctor_get(x_519, 1);
lean_inc(x_522);
lean_dec(x_519);
x_523 = lean_box(0);
lean_ctor_set(x_505, 0, x_523);
x_182 = x_505;
x_183 = x_522;
goto block_224;
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
lean_free_object(x_505);
x_524 = lean_ctor_get(x_519, 1);
lean_inc(x_524);
lean_dec(x_519);
x_525 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_226, x_516);
x_526 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_526, 0, x_525);
x_527 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_528 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_526);
x_529 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_518, x_528, x_4, x_517, x_6, x_524);
lean_dec(x_4);
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
lean_dec(x_529);
x_182 = x_530;
x_183 = x_531;
goto block_224;
}
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; uint8_t x_537; 
x_532 = lean_ctor_get(x_505, 0);
x_533 = lean_ctor_get(x_505, 1);
lean_inc(x_533);
lean_inc(x_532);
lean_dec(x_505);
x_534 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_535 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_534, x_6, x_506);
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
x_537 = lean_unbox(x_536);
lean_dec(x_536);
if (x_537 == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; 
lean_dec(x_532);
lean_dec(x_4);
x_538 = lean_ctor_get(x_535, 1);
lean_inc(x_538);
lean_dec(x_535);
x_539 = lean_box(0);
x_540 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_533);
x_182 = x_540;
x_183 = x_538;
goto block_224;
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_541 = lean_ctor_get(x_535, 1);
lean_inc(x_541);
lean_dec(x_535);
x_542 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_226, x_532);
x_543 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_543, 0, x_542);
x_544 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_545 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_543);
x_546 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_534, x_545, x_4, x_533, x_6, x_541);
lean_dec(x_4);
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_546, 1);
lean_inc(x_548);
lean_dec(x_546);
x_182 = x_547;
x_183 = x_548;
goto block_224;
}
}
}
}
else
{
lean_object* x_549; lean_object* x_550; 
x_549 = lean_ctor_get(x_498, 0);
lean_inc(x_549);
lean_dec(x_498);
x_550 = l_Lean_Syntax_getTailInfo___main(x_496);
if (lean_obj_tag(x_550) == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; uint8_t x_560; 
lean_dec(x_549);
x_551 = lean_apply_1(x_1, x_496);
x_552 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_551, x_4, x_497, x_6, x_495);
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_552, 1);
lean_inc(x_554);
lean_dec(x_552);
x_555 = lean_ctor_get(x_553, 1);
lean_inc(x_555);
lean_dec(x_553);
x_556 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_555, x_6, x_554);
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
lean_dec(x_556);
x_559 = lean_ctor_get(x_558, 4);
lean_inc(x_559);
x_560 = lean_ctor_get_uint8(x_559, sizeof(void*)*1);
lean_dec(x_559);
if (x_560 == 0)
{
uint8_t x_561; 
lean_dec(x_4);
x_561 = !lean_is_exclusive(x_557);
if (x_561 == 0)
{
lean_object* x_562; lean_object* x_563; 
x_562 = lean_ctor_get(x_557, 0);
lean_dec(x_562);
x_563 = lean_box(0);
lean_ctor_set(x_557, 0, x_563);
x_182 = x_557;
x_183 = x_558;
goto block_224;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_564 = lean_ctor_get(x_557, 1);
lean_inc(x_564);
lean_dec(x_557);
x_565 = lean_box(0);
x_566 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_564);
x_182 = x_566;
x_183 = x_558;
goto block_224;
}
}
else
{
uint8_t x_567; 
x_567 = !lean_is_exclusive(x_557);
if (x_567 == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; uint8_t x_573; 
x_568 = lean_ctor_get(x_557, 0);
x_569 = lean_ctor_get(x_557, 1);
x_570 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_571 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_570, x_6, x_558);
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
x_573 = lean_unbox(x_572);
lean_dec(x_572);
if (x_573 == 0)
{
lean_object* x_574; lean_object* x_575; 
lean_dec(x_568);
lean_dec(x_4);
x_574 = lean_ctor_get(x_571, 1);
lean_inc(x_574);
lean_dec(x_571);
x_575 = lean_box(0);
lean_ctor_set(x_557, 0, x_575);
x_182 = x_557;
x_183 = x_574;
goto block_224;
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
lean_free_object(x_557);
x_576 = lean_ctor_get(x_571, 1);
lean_inc(x_576);
lean_dec(x_571);
x_577 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_226, x_568);
x_578 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_578, 0, x_577);
x_579 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_580 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_580, 0, x_579);
lean_ctor_set(x_580, 1, x_578);
x_581 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_570, x_580, x_4, x_569, x_6, x_576);
lean_dec(x_4);
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_581, 1);
lean_inc(x_583);
lean_dec(x_581);
x_182 = x_582;
x_183 = x_583;
goto block_224;
}
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; uint8_t x_589; 
x_584 = lean_ctor_get(x_557, 0);
x_585 = lean_ctor_get(x_557, 1);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_557);
x_586 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_587 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_586, x_6, x_558);
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
x_589 = lean_unbox(x_588);
lean_dec(x_588);
if (x_589 == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
lean_dec(x_584);
lean_dec(x_4);
x_590 = lean_ctor_get(x_587, 1);
lean_inc(x_590);
lean_dec(x_587);
x_591 = lean_box(0);
x_592 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_592, 0, x_591);
lean_ctor_set(x_592, 1, x_585);
x_182 = x_592;
x_183 = x_590;
goto block_224;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_593 = lean_ctor_get(x_587, 1);
lean_inc(x_593);
lean_dec(x_587);
x_594 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_226, x_584);
x_595 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_595, 0, x_594);
x_596 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_597 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_597, 0, x_596);
lean_ctor_set(x_597, 1, x_595);
x_598 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_586, x_597, x_4, x_585, x_6, x_593);
lean_dec(x_4);
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_598, 1);
lean_inc(x_600);
lean_dec(x_598);
x_182 = x_599;
x_183 = x_600;
goto block_224;
}
}
}
}
else
{
lean_object* x_601; uint8_t x_602; 
x_601 = lean_ctor_get(x_550, 0);
lean_inc(x_601);
lean_dec(x_550);
x_602 = !lean_is_exclusive(x_549);
if (x_602 == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; uint8_t x_607; 
x_603 = lean_ctor_get(x_549, 0);
x_604 = lean_ctor_get(x_549, 1);
x_605 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14;
lean_inc(x_604);
lean_ctor_set(x_549, 0, x_605);
x_606 = l_Lean_Syntax_setHeadInfo(x_496, x_549);
x_607 = !lean_is_exclusive(x_601);
if (x_607 == 0)
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; uint8_t x_624; 
x_608 = lean_ctor_get(x_601, 1);
x_609 = lean_ctor_get(x_601, 2);
lean_inc(x_608);
lean_ctor_set(x_601, 2, x_605);
x_610 = l_Lean_Syntax_setTailInfo(x_606, x_601);
x_611 = lean_apply_1(x_1, x_610);
x_612 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_612, 0, x_603);
lean_ctor_set(x_612, 1, x_604);
lean_ctor_set(x_612, 2, x_605);
x_613 = l_Lean_Syntax_setHeadInfo(x_611, x_612);
x_614 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_614, 0, x_605);
lean_ctor_set(x_614, 1, x_608);
lean_ctor_set(x_614, 2, x_609);
x_615 = l_Lean_Syntax_setTailInfo(x_613, x_614);
x_616 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_615, x_4, x_497, x_6, x_495);
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_616, 1);
lean_inc(x_618);
lean_dec(x_616);
x_619 = lean_ctor_get(x_617, 1);
lean_inc(x_619);
lean_dec(x_617);
x_620 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_619, x_6, x_618);
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_620, 1);
lean_inc(x_622);
lean_dec(x_620);
x_623 = lean_ctor_get(x_622, 4);
lean_inc(x_623);
x_624 = lean_ctor_get_uint8(x_623, sizeof(void*)*1);
lean_dec(x_623);
if (x_624 == 0)
{
uint8_t x_625; 
lean_dec(x_4);
x_625 = !lean_is_exclusive(x_621);
if (x_625 == 0)
{
lean_object* x_626; lean_object* x_627; 
x_626 = lean_ctor_get(x_621, 0);
lean_dec(x_626);
x_627 = lean_box(0);
lean_ctor_set(x_621, 0, x_627);
x_182 = x_621;
x_183 = x_622;
goto block_224;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = lean_ctor_get(x_621, 1);
lean_inc(x_628);
lean_dec(x_621);
x_629 = lean_box(0);
x_630 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_630, 0, x_629);
lean_ctor_set(x_630, 1, x_628);
x_182 = x_630;
x_183 = x_622;
goto block_224;
}
}
else
{
uint8_t x_631; 
x_631 = !lean_is_exclusive(x_621);
if (x_631 == 0)
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; uint8_t x_637; 
x_632 = lean_ctor_get(x_621, 0);
x_633 = lean_ctor_get(x_621, 1);
x_634 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_635 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_634, x_6, x_622);
x_636 = lean_ctor_get(x_635, 0);
lean_inc(x_636);
x_637 = lean_unbox(x_636);
lean_dec(x_636);
if (x_637 == 0)
{
lean_object* x_638; lean_object* x_639; 
lean_dec(x_632);
lean_dec(x_4);
x_638 = lean_ctor_get(x_635, 1);
lean_inc(x_638);
lean_dec(x_635);
x_639 = lean_box(0);
lean_ctor_set(x_621, 0, x_639);
x_182 = x_621;
x_183 = x_638;
goto block_224;
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
lean_free_object(x_621);
x_640 = lean_ctor_get(x_635, 1);
lean_inc(x_640);
lean_dec(x_635);
x_641 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_226, x_632);
x_642 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_642, 0, x_641);
x_643 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_644 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_644, 0, x_643);
lean_ctor_set(x_644, 1, x_642);
x_645 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_634, x_644, x_4, x_633, x_6, x_640);
lean_dec(x_4);
x_646 = lean_ctor_get(x_645, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_645, 1);
lean_inc(x_647);
lean_dec(x_645);
x_182 = x_646;
x_183 = x_647;
goto block_224;
}
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; uint8_t x_653; 
x_648 = lean_ctor_get(x_621, 0);
x_649 = lean_ctor_get(x_621, 1);
lean_inc(x_649);
lean_inc(x_648);
lean_dec(x_621);
x_650 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_651 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_650, x_6, x_622);
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
x_653 = lean_unbox(x_652);
lean_dec(x_652);
if (x_653 == 0)
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; 
lean_dec(x_648);
lean_dec(x_4);
x_654 = lean_ctor_get(x_651, 1);
lean_inc(x_654);
lean_dec(x_651);
x_655 = lean_box(0);
x_656 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_656, 0, x_655);
lean_ctor_set(x_656, 1, x_649);
x_182 = x_656;
x_183 = x_654;
goto block_224;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_657 = lean_ctor_get(x_651, 1);
lean_inc(x_657);
lean_dec(x_651);
x_658 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_226, x_648);
x_659 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_659, 0, x_658);
x_660 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_661 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_661, 0, x_660);
lean_ctor_set(x_661, 1, x_659);
x_662 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_650, x_661, x_4, x_649, x_6, x_657);
lean_dec(x_4);
x_663 = lean_ctor_get(x_662, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_662, 1);
lean_inc(x_664);
lean_dec(x_662);
x_182 = x_663;
x_183 = x_664;
goto block_224;
}
}
}
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; uint8_t x_683; 
x_665 = lean_ctor_get(x_601, 0);
x_666 = lean_ctor_get(x_601, 1);
x_667 = lean_ctor_get(x_601, 2);
lean_inc(x_667);
lean_inc(x_666);
lean_inc(x_665);
lean_dec(x_601);
lean_inc(x_666);
x_668 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_668, 0, x_665);
lean_ctor_set(x_668, 1, x_666);
lean_ctor_set(x_668, 2, x_605);
x_669 = l_Lean_Syntax_setTailInfo(x_606, x_668);
x_670 = lean_apply_1(x_1, x_669);
x_671 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_671, 0, x_603);
lean_ctor_set(x_671, 1, x_604);
lean_ctor_set(x_671, 2, x_605);
x_672 = l_Lean_Syntax_setHeadInfo(x_670, x_671);
x_673 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_673, 0, x_605);
lean_ctor_set(x_673, 1, x_666);
lean_ctor_set(x_673, 2, x_667);
x_674 = l_Lean_Syntax_setTailInfo(x_672, x_673);
x_675 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_674, x_4, x_497, x_6, x_495);
x_676 = lean_ctor_get(x_675, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_675, 1);
lean_inc(x_677);
lean_dec(x_675);
x_678 = lean_ctor_get(x_676, 1);
lean_inc(x_678);
lean_dec(x_676);
x_679 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_678, x_6, x_677);
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_679, 1);
lean_inc(x_681);
lean_dec(x_679);
x_682 = lean_ctor_get(x_681, 4);
lean_inc(x_682);
x_683 = lean_ctor_get_uint8(x_682, sizeof(void*)*1);
lean_dec(x_682);
if (x_683 == 0)
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; 
lean_dec(x_4);
x_684 = lean_ctor_get(x_680, 1);
lean_inc(x_684);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_685 = x_680;
} else {
 lean_dec_ref(x_680);
 x_685 = lean_box(0);
}
x_686 = lean_box(0);
if (lean_is_scalar(x_685)) {
 x_687 = lean_alloc_ctor(0, 2, 0);
} else {
 x_687 = x_685;
}
lean_ctor_set(x_687, 0, x_686);
lean_ctor_set(x_687, 1, x_684);
x_182 = x_687;
x_183 = x_681;
goto block_224;
}
else
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; uint8_t x_694; 
x_688 = lean_ctor_get(x_680, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_680, 1);
lean_inc(x_689);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_690 = x_680;
} else {
 lean_dec_ref(x_680);
 x_690 = lean_box(0);
}
x_691 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_692 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_691, x_6, x_681);
x_693 = lean_ctor_get(x_692, 0);
lean_inc(x_693);
x_694 = lean_unbox(x_693);
lean_dec(x_693);
if (x_694 == 0)
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; 
lean_dec(x_688);
lean_dec(x_4);
x_695 = lean_ctor_get(x_692, 1);
lean_inc(x_695);
lean_dec(x_692);
x_696 = lean_box(0);
if (lean_is_scalar(x_690)) {
 x_697 = lean_alloc_ctor(0, 2, 0);
} else {
 x_697 = x_690;
}
lean_ctor_set(x_697, 0, x_696);
lean_ctor_set(x_697, 1, x_689);
x_182 = x_697;
x_183 = x_695;
goto block_224;
}
else
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; 
lean_dec(x_690);
x_698 = lean_ctor_get(x_692, 1);
lean_inc(x_698);
lean_dec(x_692);
x_699 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_226, x_688);
x_700 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_700, 0, x_699);
x_701 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_702 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_702, 0, x_701);
lean_ctor_set(x_702, 1, x_700);
x_703 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_691, x_702, x_4, x_689, x_6, x_698);
lean_dec(x_4);
x_704 = lean_ctor_get(x_703, 0);
lean_inc(x_704);
x_705 = lean_ctor_get(x_703, 1);
lean_inc(x_705);
lean_dec(x_703);
x_182 = x_704;
x_183 = x_705;
goto block_224;
}
}
}
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; uint8_t x_731; 
x_706 = lean_ctor_get(x_549, 0);
x_707 = lean_ctor_get(x_549, 1);
x_708 = lean_ctor_get(x_549, 2);
lean_inc(x_708);
lean_inc(x_707);
lean_inc(x_706);
lean_dec(x_549);
x_709 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14;
lean_inc(x_707);
x_710 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_710, 0, x_709);
lean_ctor_set(x_710, 1, x_707);
lean_ctor_set(x_710, 2, x_708);
x_711 = l_Lean_Syntax_setHeadInfo(x_496, x_710);
x_712 = lean_ctor_get(x_601, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_601, 1);
lean_inc(x_713);
x_714 = lean_ctor_get(x_601, 2);
lean_inc(x_714);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 lean_ctor_release(x_601, 2);
 x_715 = x_601;
} else {
 lean_dec_ref(x_601);
 x_715 = lean_box(0);
}
lean_inc(x_713);
if (lean_is_scalar(x_715)) {
 x_716 = lean_alloc_ctor(0, 3, 0);
} else {
 x_716 = x_715;
}
lean_ctor_set(x_716, 0, x_712);
lean_ctor_set(x_716, 1, x_713);
lean_ctor_set(x_716, 2, x_709);
x_717 = l_Lean_Syntax_setTailInfo(x_711, x_716);
x_718 = lean_apply_1(x_1, x_717);
x_719 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_719, 0, x_706);
lean_ctor_set(x_719, 1, x_707);
lean_ctor_set(x_719, 2, x_709);
x_720 = l_Lean_Syntax_setHeadInfo(x_718, x_719);
x_721 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_721, 0, x_709);
lean_ctor_set(x_721, 1, x_713);
lean_ctor_set(x_721, 2, x_714);
x_722 = l_Lean_Syntax_setTailInfo(x_720, x_721);
x_723 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_722, x_4, x_497, x_6, x_495);
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_723, 1);
lean_inc(x_725);
lean_dec(x_723);
x_726 = lean_ctor_get(x_724, 1);
lean_inc(x_726);
lean_dec(x_724);
x_727 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_726, x_6, x_725);
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_727, 1);
lean_inc(x_729);
lean_dec(x_727);
x_730 = lean_ctor_get(x_729, 4);
lean_inc(x_730);
x_731 = lean_ctor_get_uint8(x_730, sizeof(void*)*1);
lean_dec(x_730);
if (x_731 == 0)
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
lean_dec(x_4);
x_732 = lean_ctor_get(x_728, 1);
lean_inc(x_732);
if (lean_is_exclusive(x_728)) {
 lean_ctor_release(x_728, 0);
 lean_ctor_release(x_728, 1);
 x_733 = x_728;
} else {
 lean_dec_ref(x_728);
 x_733 = lean_box(0);
}
x_734 = lean_box(0);
if (lean_is_scalar(x_733)) {
 x_735 = lean_alloc_ctor(0, 2, 0);
} else {
 x_735 = x_733;
}
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set(x_735, 1, x_732);
x_182 = x_735;
x_183 = x_729;
goto block_224;
}
else
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; uint8_t x_742; 
x_736 = lean_ctor_get(x_728, 0);
lean_inc(x_736);
x_737 = lean_ctor_get(x_728, 1);
lean_inc(x_737);
if (lean_is_exclusive(x_728)) {
 lean_ctor_release(x_728, 0);
 lean_ctor_release(x_728, 1);
 x_738 = x_728;
} else {
 lean_dec_ref(x_728);
 x_738 = lean_box(0);
}
x_739 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_740 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_739, x_6, x_729);
x_741 = lean_ctor_get(x_740, 0);
lean_inc(x_741);
x_742 = lean_unbox(x_741);
lean_dec(x_741);
if (x_742 == 0)
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; 
lean_dec(x_736);
lean_dec(x_4);
x_743 = lean_ctor_get(x_740, 1);
lean_inc(x_743);
lean_dec(x_740);
x_744 = lean_box(0);
if (lean_is_scalar(x_738)) {
 x_745 = lean_alloc_ctor(0, 2, 0);
} else {
 x_745 = x_738;
}
lean_ctor_set(x_745, 0, x_744);
lean_ctor_set(x_745, 1, x_737);
x_182 = x_745;
x_183 = x_743;
goto block_224;
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
lean_dec(x_738);
x_746 = lean_ctor_get(x_740, 1);
lean_inc(x_746);
lean_dec(x_740);
x_747 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_226, x_736);
x_748 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_748, 0, x_747);
x_749 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_750 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_750, 0, x_749);
lean_ctor_set(x_750, 1, x_748);
x_751 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_739, x_750, x_4, x_737, x_6, x_746);
lean_dec(x_4);
x_752 = lean_ctor_get(x_751, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_751, 1);
lean_inc(x_753);
lean_dec(x_751);
x_182 = x_752;
x_183 = x_753;
goto block_224;
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
lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_788; uint8_t x_1040; 
x_768 = lean_ctor_get(x_177, 1);
lean_inc(x_768);
lean_dec(x_177);
x_1040 = lean_nat_dec_lt(x_176, x_2);
lean_dec(x_176);
if (x_1040 == 0)
{
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_1041 = lean_box(0);
x_1042 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1042, 0, x_1041);
lean_ctor_set(x_1042, 1, x_768);
if (lean_is_scalar(x_174)) {
 x_1043 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1043 = x_174;
}
lean_ctor_set(x_1043, 0, x_1042);
lean_ctor_set(x_1043, 1, x_178);
x_19 = x_1043;
goto block_153;
}
else
{
lean_object* x_1044; 
x_1044 = lean_ctor_get(x_18, 1);
lean_inc(x_1044);
if (lean_obj_tag(x_1044) == 0)
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
lean_dec(x_175);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_1045 = lean_box(0);
x_1046 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1046, 0, x_1045);
lean_ctor_set(x_1046, 1, x_768);
if (lean_is_scalar(x_174)) {
 x_1047 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1047 = x_174;
}
lean_ctor_set(x_1047, 0, x_1046);
lean_ctor_set(x_1047, 1, x_178);
x_19 = x_1047;
goto block_153;
}
else
{
lean_object* x_1048; lean_object* x_1049; uint8_t x_1050; 
x_1048 = lean_ctor_get(x_175, 0);
lean_inc(x_1048);
lean_dec(x_175);
x_1049 = lean_ctor_get(x_1044, 0);
lean_inc(x_1049);
lean_dec(x_1044);
x_1050 = lean_nat_dec_le(x_1048, x_1049);
lean_dec(x_1049);
lean_dec(x_1048);
if (x_1050 == 0)
{
lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_1051 = lean_box(0);
x_1052 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1052, 0, x_1051);
lean_ctor_set(x_1052, 1, x_768);
if (lean_is_scalar(x_174)) {
 x_1053 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1053 = x_174;
}
lean_ctor_set(x_1053, 0, x_1052);
lean_ctor_set(x_1053, 1, x_178);
x_19 = x_1053;
goto block_153;
}
else
{
lean_object* x_1054; 
lean_dec(x_174);
x_1054 = lean_box(0);
x_788 = x_1054;
goto block_1039;
}
}
}
}
else
{
lean_object* x_1055; 
lean_dec(x_175);
lean_dec(x_174);
x_1055 = lean_box(0);
x_788 = x_1055;
goto block_1039;
}
block_787:
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; uint8_t x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; 
x_771 = lean_ctor_get(x_769, 1);
lean_inc(x_771);
lean_dec(x_769);
x_772 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_771, x_6, x_770);
lean_dec(x_6);
x_773 = lean_ctor_get(x_772, 0);
lean_inc(x_773);
x_774 = lean_ctor_get(x_773, 1);
lean_inc(x_774);
if (lean_is_exclusive(x_773)) {
 lean_ctor_release(x_773, 0);
 lean_ctor_release(x_773, 1);
 x_775 = x_773;
} else {
 lean_dec_ref(x_773);
 x_775 = lean_box(0);
}
x_776 = lean_ctor_get(x_772, 1);
lean_inc(x_776);
if (lean_is_exclusive(x_772)) {
 lean_ctor_release(x_772, 0);
 lean_ctor_release(x_772, 1);
 x_777 = x_772;
} else {
 lean_dec_ref(x_772);
 x_777 = lean_box(0);
}
x_778 = lean_ctor_get(x_774, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_774, 2);
lean_inc(x_779);
x_780 = lean_ctor_get_uint8(x_774, sizeof(void*)*4);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 lean_ctor_release(x_774, 1);
 lean_ctor_release(x_774, 2);
 lean_ctor_release(x_774, 3);
 x_781 = x_774;
} else {
 lean_dec_ref(x_774);
 x_781 = lean_box(0);
}
x_782 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
if (lean_is_scalar(x_781)) {
 x_783 = lean_alloc_ctor(0, 4, 1);
} else {
 x_783 = x_781;
}
lean_ctor_set(x_783, 0, x_778);
lean_ctor_set(x_783, 1, x_782);
lean_ctor_set(x_783, 2, x_779);
lean_ctor_set(x_783, 3, x_155);
lean_ctor_set_uint8(x_783, sizeof(void*)*4, x_780);
x_784 = lean_box(0);
if (lean_is_scalar(x_775)) {
 x_785 = lean_alloc_ctor(0, 2, 0);
} else {
 x_785 = x_775;
}
lean_ctor_set(x_785, 0, x_784);
lean_ctor_set(x_785, 1, x_783);
if (lean_is_scalar(x_777)) {
 x_786 = lean_alloc_ctor(0, 2, 0);
} else {
 x_786 = x_777;
}
lean_ctor_set(x_786, 0, x_785);
lean_ctor_set(x_786, 1, x_776);
x_19 = x_786;
goto block_153;
}
block_1039:
{
lean_object* x_789; uint8_t x_790; 
lean_dec(x_788);
x_789 = lean_unsigned_to_nat(0u);
x_790 = lean_nat_dec_lt(x_789, x_17);
lean_dec(x_17);
if (x_790 == 0)
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; 
x_791 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_768, x_6, x_178);
x_792 = lean_ctor_get(x_791, 0);
lean_inc(x_792);
x_793 = lean_ctor_get(x_791, 1);
lean_inc(x_793);
lean_dec(x_791);
x_794 = lean_ctor_get(x_792, 0);
lean_inc(x_794);
x_795 = lean_ctor_get(x_792, 1);
lean_inc(x_795);
lean_dec(x_792);
x_796 = l_Lean_Syntax_getHeadInfo___main(x_794);
if (lean_obj_tag(x_796) == 0)
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; uint8_t x_806; 
x_797 = lean_apply_1(x_1, x_794);
x_798 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_797, x_4, x_795, x_6, x_793);
x_799 = lean_ctor_get(x_798, 0);
lean_inc(x_799);
x_800 = lean_ctor_get(x_798, 1);
lean_inc(x_800);
lean_dec(x_798);
x_801 = lean_ctor_get(x_799, 1);
lean_inc(x_801);
lean_dec(x_799);
x_802 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_801, x_6, x_800);
x_803 = lean_ctor_get(x_802, 0);
lean_inc(x_803);
x_804 = lean_ctor_get(x_802, 1);
lean_inc(x_804);
lean_dec(x_802);
x_805 = lean_ctor_get(x_804, 4);
lean_inc(x_805);
x_806 = lean_ctor_get_uint8(x_805, sizeof(void*)*1);
lean_dec(x_805);
if (x_806 == 0)
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
lean_dec(x_4);
x_807 = lean_ctor_get(x_803, 1);
lean_inc(x_807);
if (lean_is_exclusive(x_803)) {
 lean_ctor_release(x_803, 0);
 lean_ctor_release(x_803, 1);
 x_808 = x_803;
} else {
 lean_dec_ref(x_803);
 x_808 = lean_box(0);
}
x_809 = lean_box(0);
if (lean_is_scalar(x_808)) {
 x_810 = lean_alloc_ctor(0, 2, 0);
} else {
 x_810 = x_808;
}
lean_ctor_set(x_810, 0, x_809);
lean_ctor_set(x_810, 1, x_807);
x_769 = x_810;
x_770 = x_804;
goto block_787;
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; uint8_t x_817; 
x_811 = lean_ctor_get(x_803, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_803, 1);
lean_inc(x_812);
if (lean_is_exclusive(x_803)) {
 lean_ctor_release(x_803, 0);
 lean_ctor_release(x_803, 1);
 x_813 = x_803;
} else {
 lean_dec_ref(x_803);
 x_813 = lean_box(0);
}
x_814 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_815 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_814, x_6, x_804);
x_816 = lean_ctor_get(x_815, 0);
lean_inc(x_816);
x_817 = lean_unbox(x_816);
lean_dec(x_816);
if (x_817 == 0)
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; 
lean_dec(x_811);
lean_dec(x_4);
x_818 = lean_ctor_get(x_815, 1);
lean_inc(x_818);
lean_dec(x_815);
x_819 = lean_box(0);
if (lean_is_scalar(x_813)) {
 x_820 = lean_alloc_ctor(0, 2, 0);
} else {
 x_820 = x_813;
}
lean_ctor_set(x_820, 0, x_819);
lean_ctor_set(x_820, 1, x_812);
x_769 = x_820;
x_770 = x_818;
goto block_787;
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
lean_dec(x_813);
x_821 = lean_ctor_get(x_815, 1);
lean_inc(x_821);
lean_dec(x_815);
x_822 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_789, x_811);
x_823 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_823, 0, x_822);
x_824 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_825 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_825, 0, x_824);
lean_ctor_set(x_825, 1, x_823);
x_826 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_814, x_825, x_4, x_812, x_6, x_821);
lean_dec(x_4);
x_827 = lean_ctor_get(x_826, 0);
lean_inc(x_827);
x_828 = lean_ctor_get(x_826, 1);
lean_inc(x_828);
lean_dec(x_826);
x_769 = x_827;
x_770 = x_828;
goto block_787;
}
}
}
else
{
lean_object* x_829; lean_object* x_830; 
x_829 = lean_ctor_get(x_796, 0);
lean_inc(x_829);
lean_dec(x_796);
x_830 = l_Lean_Syntax_getTailInfo___main(x_794);
if (lean_obj_tag(x_830) == 0)
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; uint8_t x_840; 
lean_dec(x_829);
x_831 = lean_apply_1(x_1, x_794);
x_832 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_831, x_4, x_795, x_6, x_793);
x_833 = lean_ctor_get(x_832, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_832, 1);
lean_inc(x_834);
lean_dec(x_832);
x_835 = lean_ctor_get(x_833, 1);
lean_inc(x_835);
lean_dec(x_833);
x_836 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_835, x_6, x_834);
x_837 = lean_ctor_get(x_836, 0);
lean_inc(x_837);
x_838 = lean_ctor_get(x_836, 1);
lean_inc(x_838);
lean_dec(x_836);
x_839 = lean_ctor_get(x_838, 4);
lean_inc(x_839);
x_840 = lean_ctor_get_uint8(x_839, sizeof(void*)*1);
lean_dec(x_839);
if (x_840 == 0)
{
lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; 
lean_dec(x_4);
x_841 = lean_ctor_get(x_837, 1);
lean_inc(x_841);
if (lean_is_exclusive(x_837)) {
 lean_ctor_release(x_837, 0);
 lean_ctor_release(x_837, 1);
 x_842 = x_837;
} else {
 lean_dec_ref(x_837);
 x_842 = lean_box(0);
}
x_843 = lean_box(0);
if (lean_is_scalar(x_842)) {
 x_844 = lean_alloc_ctor(0, 2, 0);
} else {
 x_844 = x_842;
}
lean_ctor_set(x_844, 0, x_843);
lean_ctor_set(x_844, 1, x_841);
x_769 = x_844;
x_770 = x_838;
goto block_787;
}
else
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; uint8_t x_851; 
x_845 = lean_ctor_get(x_837, 0);
lean_inc(x_845);
x_846 = lean_ctor_get(x_837, 1);
lean_inc(x_846);
if (lean_is_exclusive(x_837)) {
 lean_ctor_release(x_837, 0);
 lean_ctor_release(x_837, 1);
 x_847 = x_837;
} else {
 lean_dec_ref(x_837);
 x_847 = lean_box(0);
}
x_848 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_849 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_848, x_6, x_838);
x_850 = lean_ctor_get(x_849, 0);
lean_inc(x_850);
x_851 = lean_unbox(x_850);
lean_dec(x_850);
if (x_851 == 0)
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; 
lean_dec(x_845);
lean_dec(x_4);
x_852 = lean_ctor_get(x_849, 1);
lean_inc(x_852);
lean_dec(x_849);
x_853 = lean_box(0);
if (lean_is_scalar(x_847)) {
 x_854 = lean_alloc_ctor(0, 2, 0);
} else {
 x_854 = x_847;
}
lean_ctor_set(x_854, 0, x_853);
lean_ctor_set(x_854, 1, x_846);
x_769 = x_854;
x_770 = x_852;
goto block_787;
}
else
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; 
lean_dec(x_847);
x_855 = lean_ctor_get(x_849, 1);
lean_inc(x_855);
lean_dec(x_849);
x_856 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_789, x_845);
x_857 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_857, 0, x_856);
x_858 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_859 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_859, 0, x_858);
lean_ctor_set(x_859, 1, x_857);
x_860 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_848, x_859, x_4, x_846, x_6, x_855);
lean_dec(x_4);
x_861 = lean_ctor_get(x_860, 0);
lean_inc(x_861);
x_862 = lean_ctor_get(x_860, 1);
lean_inc(x_862);
lean_dec(x_860);
x_769 = x_861;
x_770 = x_862;
goto block_787;
}
}
}
else
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; uint8_t x_890; 
x_863 = lean_ctor_get(x_830, 0);
lean_inc(x_863);
lean_dec(x_830);
x_864 = lean_ctor_get(x_829, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_829, 1);
lean_inc(x_865);
x_866 = lean_ctor_get(x_829, 2);
lean_inc(x_866);
if (lean_is_exclusive(x_829)) {
 lean_ctor_release(x_829, 0);
 lean_ctor_release(x_829, 1);
 lean_ctor_release(x_829, 2);
 x_867 = x_829;
} else {
 lean_dec_ref(x_829);
 x_867 = lean_box(0);
}
x_868 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14;
lean_inc(x_865);
if (lean_is_scalar(x_867)) {
 x_869 = lean_alloc_ctor(0, 3, 0);
} else {
 x_869 = x_867;
}
lean_ctor_set(x_869, 0, x_868);
lean_ctor_set(x_869, 1, x_865);
lean_ctor_set(x_869, 2, x_866);
x_870 = l_Lean_Syntax_setHeadInfo(x_794, x_869);
x_871 = lean_ctor_get(x_863, 0);
lean_inc(x_871);
x_872 = lean_ctor_get(x_863, 1);
lean_inc(x_872);
x_873 = lean_ctor_get(x_863, 2);
lean_inc(x_873);
if (lean_is_exclusive(x_863)) {
 lean_ctor_release(x_863, 0);
 lean_ctor_release(x_863, 1);
 lean_ctor_release(x_863, 2);
 x_874 = x_863;
} else {
 lean_dec_ref(x_863);
 x_874 = lean_box(0);
}
lean_inc(x_872);
if (lean_is_scalar(x_874)) {
 x_875 = lean_alloc_ctor(0, 3, 0);
} else {
 x_875 = x_874;
}
lean_ctor_set(x_875, 0, x_871);
lean_ctor_set(x_875, 1, x_872);
lean_ctor_set(x_875, 2, x_868);
x_876 = l_Lean_Syntax_setTailInfo(x_870, x_875);
x_877 = lean_apply_1(x_1, x_876);
x_878 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_878, 0, x_864);
lean_ctor_set(x_878, 1, x_865);
lean_ctor_set(x_878, 2, x_868);
x_879 = l_Lean_Syntax_setHeadInfo(x_877, x_878);
x_880 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_880, 0, x_868);
lean_ctor_set(x_880, 1, x_872);
lean_ctor_set(x_880, 2, x_873);
x_881 = l_Lean_Syntax_setTailInfo(x_879, x_880);
x_882 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_881, x_4, x_795, x_6, x_793);
x_883 = lean_ctor_get(x_882, 0);
lean_inc(x_883);
x_884 = lean_ctor_get(x_882, 1);
lean_inc(x_884);
lean_dec(x_882);
x_885 = lean_ctor_get(x_883, 1);
lean_inc(x_885);
lean_dec(x_883);
x_886 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_885, x_6, x_884);
x_887 = lean_ctor_get(x_886, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_886, 1);
lean_inc(x_888);
lean_dec(x_886);
x_889 = lean_ctor_get(x_888, 4);
lean_inc(x_889);
x_890 = lean_ctor_get_uint8(x_889, sizeof(void*)*1);
lean_dec(x_889);
if (x_890 == 0)
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
lean_dec(x_4);
x_891 = lean_ctor_get(x_887, 1);
lean_inc(x_891);
if (lean_is_exclusive(x_887)) {
 lean_ctor_release(x_887, 0);
 lean_ctor_release(x_887, 1);
 x_892 = x_887;
} else {
 lean_dec_ref(x_887);
 x_892 = lean_box(0);
}
x_893 = lean_box(0);
if (lean_is_scalar(x_892)) {
 x_894 = lean_alloc_ctor(0, 2, 0);
} else {
 x_894 = x_892;
}
lean_ctor_set(x_894, 0, x_893);
lean_ctor_set(x_894, 1, x_891);
x_769 = x_894;
x_770 = x_888;
goto block_787;
}
else
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; uint8_t x_901; 
x_895 = lean_ctor_get(x_887, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_887, 1);
lean_inc(x_896);
if (lean_is_exclusive(x_887)) {
 lean_ctor_release(x_887, 0);
 lean_ctor_release(x_887, 1);
 x_897 = x_887;
} else {
 lean_dec_ref(x_887);
 x_897 = lean_box(0);
}
x_898 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_899 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_898, x_6, x_888);
x_900 = lean_ctor_get(x_899, 0);
lean_inc(x_900);
x_901 = lean_unbox(x_900);
lean_dec(x_900);
if (x_901 == 0)
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; 
lean_dec(x_895);
lean_dec(x_4);
x_902 = lean_ctor_get(x_899, 1);
lean_inc(x_902);
lean_dec(x_899);
x_903 = lean_box(0);
if (lean_is_scalar(x_897)) {
 x_904 = lean_alloc_ctor(0, 2, 0);
} else {
 x_904 = x_897;
}
lean_ctor_set(x_904, 0, x_903);
lean_ctor_set(x_904, 1, x_896);
x_769 = x_904;
x_770 = x_902;
goto block_787;
}
else
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; 
lean_dec(x_897);
x_905 = lean_ctor_get(x_899, 1);
lean_inc(x_905);
lean_dec(x_899);
x_906 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_789, x_895);
x_907 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_907, 0, x_906);
x_908 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_909 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_909, 0, x_908);
lean_ctor_set(x_909, 1, x_907);
x_910 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_898, x_909, x_4, x_896, x_6, x_905);
lean_dec(x_4);
x_911 = lean_ctor_get(x_910, 0);
lean_inc(x_911);
x_912 = lean_ctor_get(x_910, 1);
lean_inc(x_912);
lean_dec(x_910);
x_769 = x_911;
x_770 = x_912;
goto block_787;
}
}
}
}
}
else
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
x_913 = l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___rarg(x_768, x_6, x_178);
x_914 = lean_ctor_get(x_913, 0);
lean_inc(x_914);
x_915 = lean_ctor_get(x_913, 1);
lean_inc(x_915);
lean_dec(x_913);
x_916 = lean_ctor_get(x_914, 1);
lean_inc(x_916);
lean_dec(x_914);
x_917 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_916, x_6, x_915);
x_918 = lean_ctor_get(x_917, 0);
lean_inc(x_918);
x_919 = lean_ctor_get(x_917, 1);
lean_inc(x_919);
lean_dec(x_917);
x_920 = lean_ctor_get(x_918, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_918, 1);
lean_inc(x_921);
lean_dec(x_918);
x_922 = l_Lean_Syntax_getHeadInfo___main(x_920);
if (lean_obj_tag(x_922) == 0)
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; uint8_t x_932; 
x_923 = lean_apply_1(x_1, x_920);
x_924 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_923, x_4, x_921, x_6, x_919);
x_925 = lean_ctor_get(x_924, 0);
lean_inc(x_925);
x_926 = lean_ctor_get(x_924, 1);
lean_inc(x_926);
lean_dec(x_924);
x_927 = lean_ctor_get(x_925, 1);
lean_inc(x_927);
lean_dec(x_925);
x_928 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_927, x_6, x_926);
x_929 = lean_ctor_get(x_928, 0);
lean_inc(x_929);
x_930 = lean_ctor_get(x_928, 1);
lean_inc(x_930);
lean_dec(x_928);
x_931 = lean_ctor_get(x_930, 4);
lean_inc(x_931);
x_932 = lean_ctor_get_uint8(x_931, sizeof(void*)*1);
lean_dec(x_931);
if (x_932 == 0)
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; 
lean_dec(x_4);
x_933 = lean_ctor_get(x_929, 1);
lean_inc(x_933);
if (lean_is_exclusive(x_929)) {
 lean_ctor_release(x_929, 0);
 lean_ctor_release(x_929, 1);
 x_934 = x_929;
} else {
 lean_dec_ref(x_929);
 x_934 = lean_box(0);
}
x_935 = lean_box(0);
if (lean_is_scalar(x_934)) {
 x_936 = lean_alloc_ctor(0, 2, 0);
} else {
 x_936 = x_934;
}
lean_ctor_set(x_936, 0, x_935);
lean_ctor_set(x_936, 1, x_933);
x_769 = x_936;
x_770 = x_930;
goto block_787;
}
else
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; uint8_t x_943; 
x_937 = lean_ctor_get(x_929, 0);
lean_inc(x_937);
x_938 = lean_ctor_get(x_929, 1);
lean_inc(x_938);
if (lean_is_exclusive(x_929)) {
 lean_ctor_release(x_929, 0);
 lean_ctor_release(x_929, 1);
 x_939 = x_929;
} else {
 lean_dec_ref(x_929);
 x_939 = lean_box(0);
}
x_940 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_941 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_940, x_6, x_930);
x_942 = lean_ctor_get(x_941, 0);
lean_inc(x_942);
x_943 = lean_unbox(x_942);
lean_dec(x_942);
if (x_943 == 0)
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; 
lean_dec(x_937);
lean_dec(x_4);
x_944 = lean_ctor_get(x_941, 1);
lean_inc(x_944);
lean_dec(x_941);
x_945 = lean_box(0);
if (lean_is_scalar(x_939)) {
 x_946 = lean_alloc_ctor(0, 2, 0);
} else {
 x_946 = x_939;
}
lean_ctor_set(x_946, 0, x_945);
lean_ctor_set(x_946, 1, x_938);
x_769 = x_946;
x_770 = x_944;
goto block_787;
}
else
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; 
lean_dec(x_939);
x_947 = lean_ctor_get(x_941, 1);
lean_inc(x_947);
lean_dec(x_941);
x_948 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_789, x_937);
x_949 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_949, 0, x_948);
x_950 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_951 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_951, 0, x_950);
lean_ctor_set(x_951, 1, x_949);
x_952 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_940, x_951, x_4, x_938, x_6, x_947);
lean_dec(x_4);
x_953 = lean_ctor_get(x_952, 0);
lean_inc(x_953);
x_954 = lean_ctor_get(x_952, 1);
lean_inc(x_954);
lean_dec(x_952);
x_769 = x_953;
x_770 = x_954;
goto block_787;
}
}
}
else
{
lean_object* x_955; lean_object* x_956; 
x_955 = lean_ctor_get(x_922, 0);
lean_inc(x_955);
lean_dec(x_922);
x_956 = l_Lean_Syntax_getTailInfo___main(x_920);
if (lean_obj_tag(x_956) == 0)
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; uint8_t x_966; 
lean_dec(x_955);
x_957 = lean_apply_1(x_1, x_920);
x_958 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_957, x_4, x_921, x_6, x_919);
x_959 = lean_ctor_get(x_958, 0);
lean_inc(x_959);
x_960 = lean_ctor_get(x_958, 1);
lean_inc(x_960);
lean_dec(x_958);
x_961 = lean_ctor_get(x_959, 1);
lean_inc(x_961);
lean_dec(x_959);
x_962 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_961, x_6, x_960);
x_963 = lean_ctor_get(x_962, 0);
lean_inc(x_963);
x_964 = lean_ctor_get(x_962, 1);
lean_inc(x_964);
lean_dec(x_962);
x_965 = lean_ctor_get(x_964, 4);
lean_inc(x_965);
x_966 = lean_ctor_get_uint8(x_965, sizeof(void*)*1);
lean_dec(x_965);
if (x_966 == 0)
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; 
lean_dec(x_4);
x_967 = lean_ctor_get(x_963, 1);
lean_inc(x_967);
if (lean_is_exclusive(x_963)) {
 lean_ctor_release(x_963, 0);
 lean_ctor_release(x_963, 1);
 x_968 = x_963;
} else {
 lean_dec_ref(x_963);
 x_968 = lean_box(0);
}
x_969 = lean_box(0);
if (lean_is_scalar(x_968)) {
 x_970 = lean_alloc_ctor(0, 2, 0);
} else {
 x_970 = x_968;
}
lean_ctor_set(x_970, 0, x_969);
lean_ctor_set(x_970, 1, x_967);
x_769 = x_970;
x_770 = x_964;
goto block_787;
}
else
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; uint8_t x_977; 
x_971 = lean_ctor_get(x_963, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_963, 1);
lean_inc(x_972);
if (lean_is_exclusive(x_963)) {
 lean_ctor_release(x_963, 0);
 lean_ctor_release(x_963, 1);
 x_973 = x_963;
} else {
 lean_dec_ref(x_963);
 x_973 = lean_box(0);
}
x_974 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_975 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_974, x_6, x_964);
x_976 = lean_ctor_get(x_975, 0);
lean_inc(x_976);
x_977 = lean_unbox(x_976);
lean_dec(x_976);
if (x_977 == 0)
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; 
lean_dec(x_971);
lean_dec(x_4);
x_978 = lean_ctor_get(x_975, 1);
lean_inc(x_978);
lean_dec(x_975);
x_979 = lean_box(0);
if (lean_is_scalar(x_973)) {
 x_980 = lean_alloc_ctor(0, 2, 0);
} else {
 x_980 = x_973;
}
lean_ctor_set(x_980, 0, x_979);
lean_ctor_set(x_980, 1, x_972);
x_769 = x_980;
x_770 = x_978;
goto block_787;
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; 
lean_dec(x_973);
x_981 = lean_ctor_get(x_975, 1);
lean_inc(x_981);
lean_dec(x_975);
x_982 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_789, x_971);
x_983 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_983, 0, x_982);
x_984 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_985 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_985, 0, x_984);
lean_ctor_set(x_985, 1, x_983);
x_986 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_974, x_985, x_4, x_972, x_6, x_981);
lean_dec(x_4);
x_987 = lean_ctor_get(x_986, 0);
lean_inc(x_987);
x_988 = lean_ctor_get(x_986, 1);
lean_inc(x_988);
lean_dec(x_986);
x_769 = x_987;
x_770 = x_988;
goto block_787;
}
}
}
else
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; uint8_t x_1016; 
x_989 = lean_ctor_get(x_956, 0);
lean_inc(x_989);
lean_dec(x_956);
x_990 = lean_ctor_get(x_955, 0);
lean_inc(x_990);
x_991 = lean_ctor_get(x_955, 1);
lean_inc(x_991);
x_992 = lean_ctor_get(x_955, 2);
lean_inc(x_992);
if (lean_is_exclusive(x_955)) {
 lean_ctor_release(x_955, 0);
 lean_ctor_release(x_955, 1);
 lean_ctor_release(x_955, 2);
 x_993 = x_955;
} else {
 lean_dec_ref(x_955);
 x_993 = lean_box(0);
}
x_994 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14;
lean_inc(x_991);
if (lean_is_scalar(x_993)) {
 x_995 = lean_alloc_ctor(0, 3, 0);
} else {
 x_995 = x_993;
}
lean_ctor_set(x_995, 0, x_994);
lean_ctor_set(x_995, 1, x_991);
lean_ctor_set(x_995, 2, x_992);
x_996 = l_Lean_Syntax_setHeadInfo(x_920, x_995);
x_997 = lean_ctor_get(x_989, 0);
lean_inc(x_997);
x_998 = lean_ctor_get(x_989, 1);
lean_inc(x_998);
x_999 = lean_ctor_get(x_989, 2);
lean_inc(x_999);
if (lean_is_exclusive(x_989)) {
 lean_ctor_release(x_989, 0);
 lean_ctor_release(x_989, 1);
 lean_ctor_release(x_989, 2);
 x_1000 = x_989;
} else {
 lean_dec_ref(x_989);
 x_1000 = lean_box(0);
}
lean_inc(x_998);
if (lean_is_scalar(x_1000)) {
 x_1001 = lean_alloc_ctor(0, 3, 0);
} else {
 x_1001 = x_1000;
}
lean_ctor_set(x_1001, 0, x_997);
lean_ctor_set(x_1001, 1, x_998);
lean_ctor_set(x_1001, 2, x_994);
x_1002 = l_Lean_Syntax_setTailInfo(x_996, x_1001);
x_1003 = lean_apply_1(x_1, x_1002);
x_1004 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1004, 0, x_990);
lean_ctor_set(x_1004, 1, x_991);
lean_ctor_set(x_1004, 2, x_994);
x_1005 = l_Lean_Syntax_setHeadInfo(x_1003, x_1004);
x_1006 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1006, 0, x_994);
lean_ctor_set(x_1006, 1, x_998);
lean_ctor_set(x_1006, 2, x_999);
x_1007 = l_Lean_Syntax_setTailInfo(x_1005, x_1006);
x_1008 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_1007, x_4, x_921, x_6, x_919);
x_1009 = lean_ctor_get(x_1008, 0);
lean_inc(x_1009);
x_1010 = lean_ctor_get(x_1008, 1);
lean_inc(x_1010);
lean_dec(x_1008);
x_1011 = lean_ctor_get(x_1009, 1);
lean_inc(x_1011);
lean_dec(x_1009);
x_1012 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_1011, x_6, x_1010);
x_1013 = lean_ctor_get(x_1012, 0);
lean_inc(x_1013);
x_1014 = lean_ctor_get(x_1012, 1);
lean_inc(x_1014);
lean_dec(x_1012);
x_1015 = lean_ctor_get(x_1014, 4);
lean_inc(x_1015);
x_1016 = lean_ctor_get_uint8(x_1015, sizeof(void*)*1);
lean_dec(x_1015);
if (x_1016 == 0)
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; 
lean_dec(x_4);
x_1017 = lean_ctor_get(x_1013, 1);
lean_inc(x_1017);
if (lean_is_exclusive(x_1013)) {
 lean_ctor_release(x_1013, 0);
 lean_ctor_release(x_1013, 1);
 x_1018 = x_1013;
} else {
 lean_dec_ref(x_1013);
 x_1018 = lean_box(0);
}
x_1019 = lean_box(0);
if (lean_is_scalar(x_1018)) {
 x_1020 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1020 = x_1018;
}
lean_ctor_set(x_1020, 0, x_1019);
lean_ctor_set(x_1020, 1, x_1017);
x_769 = x_1020;
x_770 = x_1014;
goto block_787;
}
else
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; uint8_t x_1027; 
x_1021 = lean_ctor_get(x_1013, 0);
lean_inc(x_1021);
x_1022 = lean_ctor_get(x_1013, 1);
lean_inc(x_1022);
if (lean_is_exclusive(x_1013)) {
 lean_ctor_release(x_1013, 0);
 lean_ctor_release(x_1013, 1);
 x_1023 = x_1013;
} else {
 lean_dec_ref(x_1013);
 x_1023 = lean_box(0);
}
x_1024 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1025 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1024, x_6, x_1014);
x_1026 = lean_ctor_get(x_1025, 0);
lean_inc(x_1026);
x_1027 = lean_unbox(x_1026);
lean_dec(x_1026);
if (x_1027 == 0)
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; 
lean_dec(x_1021);
lean_dec(x_4);
x_1028 = lean_ctor_get(x_1025, 1);
lean_inc(x_1028);
lean_dec(x_1025);
x_1029 = lean_box(0);
if (lean_is_scalar(x_1023)) {
 x_1030 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1030 = x_1023;
}
lean_ctor_set(x_1030, 0, x_1029);
lean_ctor_set(x_1030, 1, x_1022);
x_769 = x_1030;
x_770 = x_1028;
goto block_787;
}
else
{
lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
lean_dec(x_1023);
x_1031 = lean_ctor_get(x_1025, 1);
lean_inc(x_1031);
lean_dec(x_1025);
x_1032 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_789, x_1021);
x_1033 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1033, 0, x_1032);
x_1034 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_1035 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1035, 0, x_1034);
lean_ctor_set(x_1035, 1, x_1033);
x_1036 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1024, x_1035, x_4, x_1022, x_6, x_1031);
lean_dec(x_4);
x_1037 = lean_ctor_get(x_1036, 0);
lean_inc(x_1037);
x_1038 = lean_ctor_get(x_1036, 1);
lean_inc(x_1038);
lean_dec(x_1036);
x_769 = x_1037;
x_770 = x_1038;
goto block_787;
}
}
}
}
}
}
}
}
block_1092:
{
lean_object* x_1059; uint8_t x_1060; 
x_1059 = lean_ctor_get(x_1057, 0);
lean_inc(x_1059);
x_1060 = lean_unbox(x_1059);
lean_dec(x_1059);
if (x_1060 == 0)
{
uint8_t x_1061; 
x_1061 = !lean_is_exclusive(x_1057);
if (x_1061 == 0)
{
lean_object* x_1062; lean_object* x_1063; 
x_1062 = lean_ctor_get(x_1057, 0);
lean_dec(x_1062);
x_1063 = lean_box(0);
lean_ctor_set(x_1057, 0, x_1063);
x_177 = x_1057;
x_178 = x_1058;
goto block_1056;
}
else
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; 
x_1064 = lean_ctor_get(x_1057, 1);
lean_inc(x_1064);
lean_dec(x_1057);
x_1065 = lean_box(0);
x_1066 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1066, 0, x_1065);
lean_ctor_set(x_1066, 1, x_1064);
x_177 = x_1066;
x_178 = x_1058;
goto block_1056;
}
}
else
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; 
x_1067 = lean_ctor_get(x_1057, 1);
lean_inc(x_1067);
lean_dec(x_1057);
lean_inc(x_2);
x_1068 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_2);
x_1069 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1069, 0, x_1068);
x_1070 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__17;
x_1071 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1071, 0, x_1070);
lean_ctor_set(x_1071, 1, x_1069);
x_1072 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__20;
x_1073 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1073, 0, x_1071);
lean_ctor_set(x_1073, 1, x_1072);
lean_inc(x_176);
x_1074 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_176);
x_1075 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1075, 0, x_1074);
x_1076 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1076, 0, x_1073);
lean_ctor_set(x_1076, 1, x_1075);
x_1077 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_1078 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1078, 0, x_1076);
lean_ctor_set(x_1078, 1, x_1077);
lean_inc(x_175);
x_1079 = l_Lean_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_175);
x_1080 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1080, 0, x_1079);
x_1081 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1081, 0, x_1078);
lean_ctor_set(x_1081, 1, x_1080);
x_1082 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__23;
x_1083 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1083, 0, x_1081);
lean_ctor_set(x_1083, 1, x_1082);
x_1084 = lean_ctor_get(x_18, 1);
lean_inc(x_1084);
x_1085 = l_Lean_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_1084);
x_1086 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1086, 0, x_1085);
x_1087 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1087, 0, x_1083);
lean_ctor_set(x_1087, 1, x_1086);
x_1088 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1089 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1088, x_1087, x_4, x_1067, x_6, x_1058);
x_1090 = lean_ctor_get(x_1089, 0);
lean_inc(x_1090);
x_1091 = lean_ctor_get(x_1089, 1);
lean_inc(x_1091);
lean_dec(x_1089);
x_177 = x_1090;
x_178 = x_1091;
goto block_1056;
}
}
}
}
else
{
lean_object* x_1100; lean_object* x_1101; 
x_1100 = lean_ctor_get(x_163, 1);
lean_inc(x_1100);
lean_dec(x_163);
x_1101 = lean_ctor_get(x_1100, 2);
lean_inc(x_1101);
if (lean_obj_tag(x_1101) == 0)
{
lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_1102 = lean_ctor_get(x_162, 1);
lean_inc(x_1102);
lean_dec(x_162);
x_1103 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6;
x_1104 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__9;
x_1105 = lean_panic_fn(x_1103, x_1104);
x_1106 = lean_apply_4(x_1105, x_4, x_1100, x_6, x_1102);
return x_1106;
}
else
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1403; lean_object* x_1404; lean_object* x_1437; uint8_t x_1438; 
x_1107 = lean_ctor_get(x_162, 1);
lean_inc(x_1107);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_1108 = x_162;
} else {
 lean_dec_ref(x_162);
 x_1108 = lean_box(0);
}
x_1109 = lean_ctor_get(x_1100, 3);
lean_inc(x_1109);
x_1110 = lean_ctor_get(x_1101, 0);
lean_inc(x_1110);
lean_dec(x_1101);
x_1437 = lean_ctor_get(x_1107, 4);
lean_inc(x_1437);
x_1438 = lean_ctor_get_uint8(x_1437, sizeof(void*)*1);
lean_dec(x_1437);
if (x_1438 == 0)
{
lean_object* x_1439; lean_object* x_1440; 
x_1439 = lean_box(x_156);
x_1440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1440, 0, x_1439);
lean_ctor_set(x_1440, 1, x_1100);
x_1403 = x_1440;
x_1404 = x_1107;
goto block_1436;
}
else
{
lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; 
x_1441 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1442 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1441, x_6, x_1107);
x_1443 = lean_ctor_get(x_1442, 0);
lean_inc(x_1443);
x_1444 = lean_ctor_get(x_1442, 1);
lean_inc(x_1444);
lean_dec(x_1442);
x_1445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1445, 0, x_1443);
lean_ctor_set(x_1445, 1, x_1100);
x_1403 = x_1445;
x_1404 = x_1444;
goto block_1436;
}
block_1402:
{
lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1134; uint8_t x_1386; 
x_1113 = lean_ctor_get(x_1111, 1);
lean_inc(x_1113);
if (lean_is_exclusive(x_1111)) {
 lean_ctor_release(x_1111, 0);
 lean_ctor_release(x_1111, 1);
 x_1114 = x_1111;
} else {
 lean_dec_ref(x_1111);
 x_1114 = lean_box(0);
}
x_1386 = lean_nat_dec_lt(x_1110, x_2);
lean_dec(x_1110);
if (x_1386 == 0)
{
if (lean_obj_tag(x_1109) == 0)
{
lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_1387 = lean_box(0);
if (lean_is_scalar(x_1114)) {
 x_1388 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1388 = x_1114;
}
lean_ctor_set(x_1388, 0, x_1387);
lean_ctor_set(x_1388, 1, x_1113);
if (lean_is_scalar(x_1108)) {
 x_1389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1389 = x_1108;
}
lean_ctor_set(x_1389, 0, x_1388);
lean_ctor_set(x_1389, 1, x_1112);
x_19 = x_1389;
goto block_153;
}
else
{
lean_object* x_1390; 
x_1390 = lean_ctor_get(x_18, 1);
lean_inc(x_1390);
if (lean_obj_tag(x_1390) == 0)
{
lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; 
lean_dec(x_1109);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_1391 = lean_box(0);
if (lean_is_scalar(x_1114)) {
 x_1392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1392 = x_1114;
}
lean_ctor_set(x_1392, 0, x_1391);
lean_ctor_set(x_1392, 1, x_1113);
if (lean_is_scalar(x_1108)) {
 x_1393 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1393 = x_1108;
}
lean_ctor_set(x_1393, 0, x_1392);
lean_ctor_set(x_1393, 1, x_1112);
x_19 = x_1393;
goto block_153;
}
else
{
lean_object* x_1394; lean_object* x_1395; uint8_t x_1396; 
x_1394 = lean_ctor_get(x_1109, 0);
lean_inc(x_1394);
lean_dec(x_1109);
x_1395 = lean_ctor_get(x_1390, 0);
lean_inc(x_1395);
lean_dec(x_1390);
x_1396 = lean_nat_dec_le(x_1394, x_1395);
lean_dec(x_1395);
lean_dec(x_1394);
if (x_1396 == 0)
{
lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_1397 = lean_box(0);
if (lean_is_scalar(x_1114)) {
 x_1398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1398 = x_1114;
}
lean_ctor_set(x_1398, 0, x_1397);
lean_ctor_set(x_1398, 1, x_1113);
if (lean_is_scalar(x_1108)) {
 x_1399 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1399 = x_1108;
}
lean_ctor_set(x_1399, 0, x_1398);
lean_ctor_set(x_1399, 1, x_1112);
x_19 = x_1399;
goto block_153;
}
else
{
lean_object* x_1400; 
lean_dec(x_1114);
lean_dec(x_1108);
x_1400 = lean_box(0);
x_1134 = x_1400;
goto block_1385;
}
}
}
}
else
{
lean_object* x_1401; 
lean_dec(x_1114);
lean_dec(x_1109);
lean_dec(x_1108);
x_1401 = lean_box(0);
x_1134 = x_1401;
goto block_1385;
}
block_1133:
{
lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; uint8_t x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
x_1117 = lean_ctor_get(x_1115, 1);
lean_inc(x_1117);
lean_dec(x_1115);
x_1118 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_1117, x_6, x_1116);
lean_dec(x_6);
x_1119 = lean_ctor_get(x_1118, 0);
lean_inc(x_1119);
x_1120 = lean_ctor_get(x_1119, 1);
lean_inc(x_1120);
if (lean_is_exclusive(x_1119)) {
 lean_ctor_release(x_1119, 0);
 lean_ctor_release(x_1119, 1);
 x_1121 = x_1119;
} else {
 lean_dec_ref(x_1119);
 x_1121 = lean_box(0);
}
x_1122 = lean_ctor_get(x_1118, 1);
lean_inc(x_1122);
if (lean_is_exclusive(x_1118)) {
 lean_ctor_release(x_1118, 0);
 lean_ctor_release(x_1118, 1);
 x_1123 = x_1118;
} else {
 lean_dec_ref(x_1118);
 x_1123 = lean_box(0);
}
x_1124 = lean_ctor_get(x_1120, 0);
lean_inc(x_1124);
x_1125 = lean_ctor_get(x_1120, 2);
lean_inc(x_1125);
x_1126 = lean_ctor_get_uint8(x_1120, sizeof(void*)*4);
if (lean_is_exclusive(x_1120)) {
 lean_ctor_release(x_1120, 0);
 lean_ctor_release(x_1120, 1);
 lean_ctor_release(x_1120, 2);
 lean_ctor_release(x_1120, 3);
 x_1127 = x_1120;
} else {
 lean_dec_ref(x_1120);
 x_1127 = lean_box(0);
}
x_1128 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
if (lean_is_scalar(x_1127)) {
 x_1129 = lean_alloc_ctor(0, 4, 1);
} else {
 x_1129 = x_1127;
}
lean_ctor_set(x_1129, 0, x_1124);
lean_ctor_set(x_1129, 1, x_1128);
lean_ctor_set(x_1129, 2, x_1125);
lean_ctor_set(x_1129, 3, x_155);
lean_ctor_set_uint8(x_1129, sizeof(void*)*4, x_1126);
x_1130 = lean_box(0);
if (lean_is_scalar(x_1121)) {
 x_1131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1131 = x_1121;
}
lean_ctor_set(x_1131, 0, x_1130);
lean_ctor_set(x_1131, 1, x_1129);
if (lean_is_scalar(x_1123)) {
 x_1132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1132 = x_1123;
}
lean_ctor_set(x_1132, 0, x_1131);
lean_ctor_set(x_1132, 1, x_1122);
x_19 = x_1132;
goto block_153;
}
block_1385:
{
lean_object* x_1135; uint8_t x_1136; 
lean_dec(x_1134);
x_1135 = lean_unsigned_to_nat(0u);
x_1136 = lean_nat_dec_lt(x_1135, x_17);
lean_dec(x_17);
if (x_1136 == 0)
{
lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; 
x_1137 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_1113, x_6, x_1112);
x_1138 = lean_ctor_get(x_1137, 0);
lean_inc(x_1138);
x_1139 = lean_ctor_get(x_1137, 1);
lean_inc(x_1139);
lean_dec(x_1137);
x_1140 = lean_ctor_get(x_1138, 0);
lean_inc(x_1140);
x_1141 = lean_ctor_get(x_1138, 1);
lean_inc(x_1141);
lean_dec(x_1138);
x_1142 = l_Lean_Syntax_getHeadInfo___main(x_1140);
if (lean_obj_tag(x_1142) == 0)
{
lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; uint8_t x_1152; 
x_1143 = lean_apply_1(x_1, x_1140);
x_1144 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_1143, x_4, x_1141, x_6, x_1139);
x_1145 = lean_ctor_get(x_1144, 0);
lean_inc(x_1145);
x_1146 = lean_ctor_get(x_1144, 1);
lean_inc(x_1146);
lean_dec(x_1144);
x_1147 = lean_ctor_get(x_1145, 1);
lean_inc(x_1147);
lean_dec(x_1145);
x_1148 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_1147, x_6, x_1146);
x_1149 = lean_ctor_get(x_1148, 0);
lean_inc(x_1149);
x_1150 = lean_ctor_get(x_1148, 1);
lean_inc(x_1150);
lean_dec(x_1148);
x_1151 = lean_ctor_get(x_1150, 4);
lean_inc(x_1151);
x_1152 = lean_ctor_get_uint8(x_1151, sizeof(void*)*1);
lean_dec(x_1151);
if (x_1152 == 0)
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; 
lean_dec(x_4);
x_1153 = lean_ctor_get(x_1149, 1);
lean_inc(x_1153);
if (lean_is_exclusive(x_1149)) {
 lean_ctor_release(x_1149, 0);
 lean_ctor_release(x_1149, 1);
 x_1154 = x_1149;
} else {
 lean_dec_ref(x_1149);
 x_1154 = lean_box(0);
}
x_1155 = lean_box(0);
if (lean_is_scalar(x_1154)) {
 x_1156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1156 = x_1154;
}
lean_ctor_set(x_1156, 0, x_1155);
lean_ctor_set(x_1156, 1, x_1153);
x_1115 = x_1156;
x_1116 = x_1150;
goto block_1133;
}
else
{
lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; uint8_t x_1163; 
x_1157 = lean_ctor_get(x_1149, 0);
lean_inc(x_1157);
x_1158 = lean_ctor_get(x_1149, 1);
lean_inc(x_1158);
if (lean_is_exclusive(x_1149)) {
 lean_ctor_release(x_1149, 0);
 lean_ctor_release(x_1149, 1);
 x_1159 = x_1149;
} else {
 lean_dec_ref(x_1149);
 x_1159 = lean_box(0);
}
x_1160 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1161 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1160, x_6, x_1150);
x_1162 = lean_ctor_get(x_1161, 0);
lean_inc(x_1162);
x_1163 = lean_unbox(x_1162);
lean_dec(x_1162);
if (x_1163 == 0)
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; 
lean_dec(x_1157);
lean_dec(x_4);
x_1164 = lean_ctor_get(x_1161, 1);
lean_inc(x_1164);
lean_dec(x_1161);
x_1165 = lean_box(0);
if (lean_is_scalar(x_1159)) {
 x_1166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1166 = x_1159;
}
lean_ctor_set(x_1166, 0, x_1165);
lean_ctor_set(x_1166, 1, x_1158);
x_1115 = x_1166;
x_1116 = x_1164;
goto block_1133;
}
else
{
lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; 
lean_dec(x_1159);
x_1167 = lean_ctor_get(x_1161, 1);
lean_inc(x_1167);
lean_dec(x_1161);
x_1168 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_1135, x_1157);
x_1169 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1169, 0, x_1168);
x_1170 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_1171 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1171, 0, x_1170);
lean_ctor_set(x_1171, 1, x_1169);
x_1172 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1160, x_1171, x_4, x_1158, x_6, x_1167);
lean_dec(x_4);
x_1173 = lean_ctor_get(x_1172, 0);
lean_inc(x_1173);
x_1174 = lean_ctor_get(x_1172, 1);
lean_inc(x_1174);
lean_dec(x_1172);
x_1115 = x_1173;
x_1116 = x_1174;
goto block_1133;
}
}
}
else
{
lean_object* x_1175; lean_object* x_1176; 
x_1175 = lean_ctor_get(x_1142, 0);
lean_inc(x_1175);
lean_dec(x_1142);
x_1176 = l_Lean_Syntax_getTailInfo___main(x_1140);
if (lean_obj_tag(x_1176) == 0)
{
lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; uint8_t x_1186; 
lean_dec(x_1175);
x_1177 = lean_apply_1(x_1, x_1140);
x_1178 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_1177, x_4, x_1141, x_6, x_1139);
x_1179 = lean_ctor_get(x_1178, 0);
lean_inc(x_1179);
x_1180 = lean_ctor_get(x_1178, 1);
lean_inc(x_1180);
lean_dec(x_1178);
x_1181 = lean_ctor_get(x_1179, 1);
lean_inc(x_1181);
lean_dec(x_1179);
x_1182 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_1181, x_6, x_1180);
x_1183 = lean_ctor_get(x_1182, 0);
lean_inc(x_1183);
x_1184 = lean_ctor_get(x_1182, 1);
lean_inc(x_1184);
lean_dec(x_1182);
x_1185 = lean_ctor_get(x_1184, 4);
lean_inc(x_1185);
x_1186 = lean_ctor_get_uint8(x_1185, sizeof(void*)*1);
lean_dec(x_1185);
if (x_1186 == 0)
{
lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; 
lean_dec(x_4);
x_1187 = lean_ctor_get(x_1183, 1);
lean_inc(x_1187);
if (lean_is_exclusive(x_1183)) {
 lean_ctor_release(x_1183, 0);
 lean_ctor_release(x_1183, 1);
 x_1188 = x_1183;
} else {
 lean_dec_ref(x_1183);
 x_1188 = lean_box(0);
}
x_1189 = lean_box(0);
if (lean_is_scalar(x_1188)) {
 x_1190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1190 = x_1188;
}
lean_ctor_set(x_1190, 0, x_1189);
lean_ctor_set(x_1190, 1, x_1187);
x_1115 = x_1190;
x_1116 = x_1184;
goto block_1133;
}
else
{
lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; uint8_t x_1197; 
x_1191 = lean_ctor_get(x_1183, 0);
lean_inc(x_1191);
x_1192 = lean_ctor_get(x_1183, 1);
lean_inc(x_1192);
if (lean_is_exclusive(x_1183)) {
 lean_ctor_release(x_1183, 0);
 lean_ctor_release(x_1183, 1);
 x_1193 = x_1183;
} else {
 lean_dec_ref(x_1183);
 x_1193 = lean_box(0);
}
x_1194 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1195 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1194, x_6, x_1184);
x_1196 = lean_ctor_get(x_1195, 0);
lean_inc(x_1196);
x_1197 = lean_unbox(x_1196);
lean_dec(x_1196);
if (x_1197 == 0)
{
lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; 
lean_dec(x_1191);
lean_dec(x_4);
x_1198 = lean_ctor_get(x_1195, 1);
lean_inc(x_1198);
lean_dec(x_1195);
x_1199 = lean_box(0);
if (lean_is_scalar(x_1193)) {
 x_1200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1200 = x_1193;
}
lean_ctor_set(x_1200, 0, x_1199);
lean_ctor_set(x_1200, 1, x_1192);
x_1115 = x_1200;
x_1116 = x_1198;
goto block_1133;
}
else
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; 
lean_dec(x_1193);
x_1201 = lean_ctor_get(x_1195, 1);
lean_inc(x_1201);
lean_dec(x_1195);
x_1202 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_1135, x_1191);
x_1203 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1203, 0, x_1202);
x_1204 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_1205 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1205, 0, x_1204);
lean_ctor_set(x_1205, 1, x_1203);
x_1206 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1194, x_1205, x_4, x_1192, x_6, x_1201);
lean_dec(x_4);
x_1207 = lean_ctor_get(x_1206, 0);
lean_inc(x_1207);
x_1208 = lean_ctor_get(x_1206, 1);
lean_inc(x_1208);
lean_dec(x_1206);
x_1115 = x_1207;
x_1116 = x_1208;
goto block_1133;
}
}
}
else
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; uint8_t x_1236; 
x_1209 = lean_ctor_get(x_1176, 0);
lean_inc(x_1209);
lean_dec(x_1176);
x_1210 = lean_ctor_get(x_1175, 0);
lean_inc(x_1210);
x_1211 = lean_ctor_get(x_1175, 1);
lean_inc(x_1211);
x_1212 = lean_ctor_get(x_1175, 2);
lean_inc(x_1212);
if (lean_is_exclusive(x_1175)) {
 lean_ctor_release(x_1175, 0);
 lean_ctor_release(x_1175, 1);
 lean_ctor_release(x_1175, 2);
 x_1213 = x_1175;
} else {
 lean_dec_ref(x_1175);
 x_1213 = lean_box(0);
}
x_1214 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14;
lean_inc(x_1211);
if (lean_is_scalar(x_1213)) {
 x_1215 = lean_alloc_ctor(0, 3, 0);
} else {
 x_1215 = x_1213;
}
lean_ctor_set(x_1215, 0, x_1214);
lean_ctor_set(x_1215, 1, x_1211);
lean_ctor_set(x_1215, 2, x_1212);
x_1216 = l_Lean_Syntax_setHeadInfo(x_1140, x_1215);
x_1217 = lean_ctor_get(x_1209, 0);
lean_inc(x_1217);
x_1218 = lean_ctor_get(x_1209, 1);
lean_inc(x_1218);
x_1219 = lean_ctor_get(x_1209, 2);
lean_inc(x_1219);
if (lean_is_exclusive(x_1209)) {
 lean_ctor_release(x_1209, 0);
 lean_ctor_release(x_1209, 1);
 lean_ctor_release(x_1209, 2);
 x_1220 = x_1209;
} else {
 lean_dec_ref(x_1209);
 x_1220 = lean_box(0);
}
lean_inc(x_1218);
if (lean_is_scalar(x_1220)) {
 x_1221 = lean_alloc_ctor(0, 3, 0);
} else {
 x_1221 = x_1220;
}
lean_ctor_set(x_1221, 0, x_1217);
lean_ctor_set(x_1221, 1, x_1218);
lean_ctor_set(x_1221, 2, x_1214);
x_1222 = l_Lean_Syntax_setTailInfo(x_1216, x_1221);
x_1223 = lean_apply_1(x_1, x_1222);
x_1224 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1224, 0, x_1210);
lean_ctor_set(x_1224, 1, x_1211);
lean_ctor_set(x_1224, 2, x_1214);
x_1225 = l_Lean_Syntax_setHeadInfo(x_1223, x_1224);
x_1226 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1226, 0, x_1214);
lean_ctor_set(x_1226, 1, x_1218);
lean_ctor_set(x_1226, 2, x_1219);
x_1227 = l_Lean_Syntax_setTailInfo(x_1225, x_1226);
x_1228 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_1227, x_4, x_1141, x_6, x_1139);
x_1229 = lean_ctor_get(x_1228, 0);
lean_inc(x_1229);
x_1230 = lean_ctor_get(x_1228, 1);
lean_inc(x_1230);
lean_dec(x_1228);
x_1231 = lean_ctor_get(x_1229, 1);
lean_inc(x_1231);
lean_dec(x_1229);
x_1232 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_1231, x_6, x_1230);
x_1233 = lean_ctor_get(x_1232, 0);
lean_inc(x_1233);
x_1234 = lean_ctor_get(x_1232, 1);
lean_inc(x_1234);
lean_dec(x_1232);
x_1235 = lean_ctor_get(x_1234, 4);
lean_inc(x_1235);
x_1236 = lean_ctor_get_uint8(x_1235, sizeof(void*)*1);
lean_dec(x_1235);
if (x_1236 == 0)
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; 
lean_dec(x_4);
x_1237 = lean_ctor_get(x_1233, 1);
lean_inc(x_1237);
if (lean_is_exclusive(x_1233)) {
 lean_ctor_release(x_1233, 0);
 lean_ctor_release(x_1233, 1);
 x_1238 = x_1233;
} else {
 lean_dec_ref(x_1233);
 x_1238 = lean_box(0);
}
x_1239 = lean_box(0);
if (lean_is_scalar(x_1238)) {
 x_1240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1240 = x_1238;
}
lean_ctor_set(x_1240, 0, x_1239);
lean_ctor_set(x_1240, 1, x_1237);
x_1115 = x_1240;
x_1116 = x_1234;
goto block_1133;
}
else
{
lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; uint8_t x_1247; 
x_1241 = lean_ctor_get(x_1233, 0);
lean_inc(x_1241);
x_1242 = lean_ctor_get(x_1233, 1);
lean_inc(x_1242);
if (lean_is_exclusive(x_1233)) {
 lean_ctor_release(x_1233, 0);
 lean_ctor_release(x_1233, 1);
 x_1243 = x_1233;
} else {
 lean_dec_ref(x_1233);
 x_1243 = lean_box(0);
}
x_1244 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1245 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1244, x_6, x_1234);
x_1246 = lean_ctor_get(x_1245, 0);
lean_inc(x_1246);
x_1247 = lean_unbox(x_1246);
lean_dec(x_1246);
if (x_1247 == 0)
{
lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; 
lean_dec(x_1241);
lean_dec(x_4);
x_1248 = lean_ctor_get(x_1245, 1);
lean_inc(x_1248);
lean_dec(x_1245);
x_1249 = lean_box(0);
if (lean_is_scalar(x_1243)) {
 x_1250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1250 = x_1243;
}
lean_ctor_set(x_1250, 0, x_1249);
lean_ctor_set(x_1250, 1, x_1242);
x_1115 = x_1250;
x_1116 = x_1248;
goto block_1133;
}
else
{
lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; 
lean_dec(x_1243);
x_1251 = lean_ctor_get(x_1245, 1);
lean_inc(x_1251);
lean_dec(x_1245);
x_1252 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_1135, x_1241);
x_1253 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1253, 0, x_1252);
x_1254 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_1255 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1255, 0, x_1254);
lean_ctor_set(x_1255, 1, x_1253);
x_1256 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1244, x_1255, x_4, x_1242, x_6, x_1251);
lean_dec(x_4);
x_1257 = lean_ctor_get(x_1256, 0);
lean_inc(x_1257);
x_1258 = lean_ctor_get(x_1256, 1);
lean_inc(x_1258);
lean_dec(x_1256);
x_1115 = x_1257;
x_1116 = x_1258;
goto block_1133;
}
}
}
}
}
else
{
lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; 
x_1259 = l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___rarg(x_1113, x_6, x_1112);
x_1260 = lean_ctor_get(x_1259, 0);
lean_inc(x_1260);
x_1261 = lean_ctor_get(x_1259, 1);
lean_inc(x_1261);
lean_dec(x_1259);
x_1262 = lean_ctor_get(x_1260, 1);
lean_inc(x_1262);
lean_dec(x_1260);
x_1263 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_1262, x_6, x_1261);
x_1264 = lean_ctor_get(x_1263, 0);
lean_inc(x_1264);
x_1265 = lean_ctor_get(x_1263, 1);
lean_inc(x_1265);
lean_dec(x_1263);
x_1266 = lean_ctor_get(x_1264, 0);
lean_inc(x_1266);
x_1267 = lean_ctor_get(x_1264, 1);
lean_inc(x_1267);
lean_dec(x_1264);
x_1268 = l_Lean_Syntax_getHeadInfo___main(x_1266);
if (lean_obj_tag(x_1268) == 0)
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; uint8_t x_1278; 
x_1269 = lean_apply_1(x_1, x_1266);
x_1270 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_1269, x_4, x_1267, x_6, x_1265);
x_1271 = lean_ctor_get(x_1270, 0);
lean_inc(x_1271);
x_1272 = lean_ctor_get(x_1270, 1);
lean_inc(x_1272);
lean_dec(x_1270);
x_1273 = lean_ctor_get(x_1271, 1);
lean_inc(x_1273);
lean_dec(x_1271);
x_1274 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_1273, x_6, x_1272);
x_1275 = lean_ctor_get(x_1274, 0);
lean_inc(x_1275);
x_1276 = lean_ctor_get(x_1274, 1);
lean_inc(x_1276);
lean_dec(x_1274);
x_1277 = lean_ctor_get(x_1276, 4);
lean_inc(x_1277);
x_1278 = lean_ctor_get_uint8(x_1277, sizeof(void*)*1);
lean_dec(x_1277);
if (x_1278 == 0)
{
lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; 
lean_dec(x_4);
x_1279 = lean_ctor_get(x_1275, 1);
lean_inc(x_1279);
if (lean_is_exclusive(x_1275)) {
 lean_ctor_release(x_1275, 0);
 lean_ctor_release(x_1275, 1);
 x_1280 = x_1275;
} else {
 lean_dec_ref(x_1275);
 x_1280 = lean_box(0);
}
x_1281 = lean_box(0);
if (lean_is_scalar(x_1280)) {
 x_1282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1282 = x_1280;
}
lean_ctor_set(x_1282, 0, x_1281);
lean_ctor_set(x_1282, 1, x_1279);
x_1115 = x_1282;
x_1116 = x_1276;
goto block_1133;
}
else
{
lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; uint8_t x_1289; 
x_1283 = lean_ctor_get(x_1275, 0);
lean_inc(x_1283);
x_1284 = lean_ctor_get(x_1275, 1);
lean_inc(x_1284);
if (lean_is_exclusive(x_1275)) {
 lean_ctor_release(x_1275, 0);
 lean_ctor_release(x_1275, 1);
 x_1285 = x_1275;
} else {
 lean_dec_ref(x_1275);
 x_1285 = lean_box(0);
}
x_1286 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1287 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1286, x_6, x_1276);
x_1288 = lean_ctor_get(x_1287, 0);
lean_inc(x_1288);
x_1289 = lean_unbox(x_1288);
lean_dec(x_1288);
if (x_1289 == 0)
{
lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; 
lean_dec(x_1283);
lean_dec(x_4);
x_1290 = lean_ctor_get(x_1287, 1);
lean_inc(x_1290);
lean_dec(x_1287);
x_1291 = lean_box(0);
if (lean_is_scalar(x_1285)) {
 x_1292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1292 = x_1285;
}
lean_ctor_set(x_1292, 0, x_1291);
lean_ctor_set(x_1292, 1, x_1284);
x_1115 = x_1292;
x_1116 = x_1290;
goto block_1133;
}
else
{
lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; 
lean_dec(x_1285);
x_1293 = lean_ctor_get(x_1287, 1);
lean_inc(x_1293);
lean_dec(x_1287);
x_1294 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_1135, x_1283);
x_1295 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1295, 0, x_1294);
x_1296 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_1297 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1297, 0, x_1296);
lean_ctor_set(x_1297, 1, x_1295);
x_1298 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1286, x_1297, x_4, x_1284, x_6, x_1293);
lean_dec(x_4);
x_1299 = lean_ctor_get(x_1298, 0);
lean_inc(x_1299);
x_1300 = lean_ctor_get(x_1298, 1);
lean_inc(x_1300);
lean_dec(x_1298);
x_1115 = x_1299;
x_1116 = x_1300;
goto block_1133;
}
}
}
else
{
lean_object* x_1301; lean_object* x_1302; 
x_1301 = lean_ctor_get(x_1268, 0);
lean_inc(x_1301);
lean_dec(x_1268);
x_1302 = l_Lean_Syntax_getTailInfo___main(x_1266);
if (lean_obj_tag(x_1302) == 0)
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; uint8_t x_1312; 
lean_dec(x_1301);
x_1303 = lean_apply_1(x_1, x_1266);
x_1304 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_1303, x_4, x_1267, x_6, x_1265);
x_1305 = lean_ctor_get(x_1304, 0);
lean_inc(x_1305);
x_1306 = lean_ctor_get(x_1304, 1);
lean_inc(x_1306);
lean_dec(x_1304);
x_1307 = lean_ctor_get(x_1305, 1);
lean_inc(x_1307);
lean_dec(x_1305);
x_1308 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_1307, x_6, x_1306);
x_1309 = lean_ctor_get(x_1308, 0);
lean_inc(x_1309);
x_1310 = lean_ctor_get(x_1308, 1);
lean_inc(x_1310);
lean_dec(x_1308);
x_1311 = lean_ctor_get(x_1310, 4);
lean_inc(x_1311);
x_1312 = lean_ctor_get_uint8(x_1311, sizeof(void*)*1);
lean_dec(x_1311);
if (x_1312 == 0)
{
lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; 
lean_dec(x_4);
x_1313 = lean_ctor_get(x_1309, 1);
lean_inc(x_1313);
if (lean_is_exclusive(x_1309)) {
 lean_ctor_release(x_1309, 0);
 lean_ctor_release(x_1309, 1);
 x_1314 = x_1309;
} else {
 lean_dec_ref(x_1309);
 x_1314 = lean_box(0);
}
x_1315 = lean_box(0);
if (lean_is_scalar(x_1314)) {
 x_1316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1316 = x_1314;
}
lean_ctor_set(x_1316, 0, x_1315);
lean_ctor_set(x_1316, 1, x_1313);
x_1115 = x_1316;
x_1116 = x_1310;
goto block_1133;
}
else
{
lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; uint8_t x_1323; 
x_1317 = lean_ctor_get(x_1309, 0);
lean_inc(x_1317);
x_1318 = lean_ctor_get(x_1309, 1);
lean_inc(x_1318);
if (lean_is_exclusive(x_1309)) {
 lean_ctor_release(x_1309, 0);
 lean_ctor_release(x_1309, 1);
 x_1319 = x_1309;
} else {
 lean_dec_ref(x_1309);
 x_1319 = lean_box(0);
}
x_1320 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1321 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1320, x_6, x_1310);
x_1322 = lean_ctor_get(x_1321, 0);
lean_inc(x_1322);
x_1323 = lean_unbox(x_1322);
lean_dec(x_1322);
if (x_1323 == 0)
{
lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; 
lean_dec(x_1317);
lean_dec(x_4);
x_1324 = lean_ctor_get(x_1321, 1);
lean_inc(x_1324);
lean_dec(x_1321);
x_1325 = lean_box(0);
if (lean_is_scalar(x_1319)) {
 x_1326 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1326 = x_1319;
}
lean_ctor_set(x_1326, 0, x_1325);
lean_ctor_set(x_1326, 1, x_1318);
x_1115 = x_1326;
x_1116 = x_1324;
goto block_1133;
}
else
{
lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; 
lean_dec(x_1319);
x_1327 = lean_ctor_get(x_1321, 1);
lean_inc(x_1327);
lean_dec(x_1321);
x_1328 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_1135, x_1317);
x_1329 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1329, 0, x_1328);
x_1330 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_1331 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1331, 0, x_1330);
lean_ctor_set(x_1331, 1, x_1329);
x_1332 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1320, x_1331, x_4, x_1318, x_6, x_1327);
lean_dec(x_4);
x_1333 = lean_ctor_get(x_1332, 0);
lean_inc(x_1333);
x_1334 = lean_ctor_get(x_1332, 1);
lean_inc(x_1334);
lean_dec(x_1332);
x_1115 = x_1333;
x_1116 = x_1334;
goto block_1133;
}
}
}
else
{
lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; uint8_t x_1362; 
x_1335 = lean_ctor_get(x_1302, 0);
lean_inc(x_1335);
lean_dec(x_1302);
x_1336 = lean_ctor_get(x_1301, 0);
lean_inc(x_1336);
x_1337 = lean_ctor_get(x_1301, 1);
lean_inc(x_1337);
x_1338 = lean_ctor_get(x_1301, 2);
lean_inc(x_1338);
if (lean_is_exclusive(x_1301)) {
 lean_ctor_release(x_1301, 0);
 lean_ctor_release(x_1301, 1);
 lean_ctor_release(x_1301, 2);
 x_1339 = x_1301;
} else {
 lean_dec_ref(x_1301);
 x_1339 = lean_box(0);
}
x_1340 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14;
lean_inc(x_1337);
if (lean_is_scalar(x_1339)) {
 x_1341 = lean_alloc_ctor(0, 3, 0);
} else {
 x_1341 = x_1339;
}
lean_ctor_set(x_1341, 0, x_1340);
lean_ctor_set(x_1341, 1, x_1337);
lean_ctor_set(x_1341, 2, x_1338);
x_1342 = l_Lean_Syntax_setHeadInfo(x_1266, x_1341);
x_1343 = lean_ctor_get(x_1335, 0);
lean_inc(x_1343);
x_1344 = lean_ctor_get(x_1335, 1);
lean_inc(x_1344);
x_1345 = lean_ctor_get(x_1335, 2);
lean_inc(x_1345);
if (lean_is_exclusive(x_1335)) {
 lean_ctor_release(x_1335, 0);
 lean_ctor_release(x_1335, 1);
 lean_ctor_release(x_1335, 2);
 x_1346 = x_1335;
} else {
 lean_dec_ref(x_1335);
 x_1346 = lean_box(0);
}
lean_inc(x_1344);
if (lean_is_scalar(x_1346)) {
 x_1347 = lean_alloc_ctor(0, 3, 0);
} else {
 x_1347 = x_1346;
}
lean_ctor_set(x_1347, 0, x_1343);
lean_ctor_set(x_1347, 1, x_1344);
lean_ctor_set(x_1347, 2, x_1340);
x_1348 = l_Lean_Syntax_setTailInfo(x_1342, x_1347);
x_1349 = lean_apply_1(x_1, x_1348);
x_1350 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1350, 0, x_1336);
lean_ctor_set(x_1350, 1, x_1337);
lean_ctor_set(x_1350, 2, x_1340);
x_1351 = l_Lean_Syntax_setHeadInfo(x_1349, x_1350);
x_1352 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1352, 0, x_1340);
lean_ctor_set(x_1352, 1, x_1344);
lean_ctor_set(x_1352, 2, x_1345);
x_1353 = l_Lean_Syntax_setTailInfo(x_1351, x_1352);
x_1354 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_1353, x_4, x_1267, x_6, x_1265);
x_1355 = lean_ctor_get(x_1354, 0);
lean_inc(x_1355);
x_1356 = lean_ctor_get(x_1354, 1);
lean_inc(x_1356);
lean_dec(x_1354);
x_1357 = lean_ctor_get(x_1355, 1);
lean_inc(x_1357);
lean_dec(x_1355);
x_1358 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_1357, x_6, x_1356);
x_1359 = lean_ctor_get(x_1358, 0);
lean_inc(x_1359);
x_1360 = lean_ctor_get(x_1358, 1);
lean_inc(x_1360);
lean_dec(x_1358);
x_1361 = lean_ctor_get(x_1360, 4);
lean_inc(x_1361);
x_1362 = lean_ctor_get_uint8(x_1361, sizeof(void*)*1);
lean_dec(x_1361);
if (x_1362 == 0)
{
lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; 
lean_dec(x_4);
x_1363 = lean_ctor_get(x_1359, 1);
lean_inc(x_1363);
if (lean_is_exclusive(x_1359)) {
 lean_ctor_release(x_1359, 0);
 lean_ctor_release(x_1359, 1);
 x_1364 = x_1359;
} else {
 lean_dec_ref(x_1359);
 x_1364 = lean_box(0);
}
x_1365 = lean_box(0);
if (lean_is_scalar(x_1364)) {
 x_1366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1366 = x_1364;
}
lean_ctor_set(x_1366, 0, x_1365);
lean_ctor_set(x_1366, 1, x_1363);
x_1115 = x_1366;
x_1116 = x_1360;
goto block_1133;
}
else
{
lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; uint8_t x_1373; 
x_1367 = lean_ctor_get(x_1359, 0);
lean_inc(x_1367);
x_1368 = lean_ctor_get(x_1359, 1);
lean_inc(x_1368);
if (lean_is_exclusive(x_1359)) {
 lean_ctor_release(x_1359, 0);
 lean_ctor_release(x_1359, 1);
 x_1369 = x_1359;
} else {
 lean_dec_ref(x_1359);
 x_1369 = lean_box(0);
}
x_1370 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1371 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1370, x_6, x_1360);
x_1372 = lean_ctor_get(x_1371, 0);
lean_inc(x_1372);
x_1373 = lean_unbox(x_1372);
lean_dec(x_1372);
if (x_1373 == 0)
{
lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; 
lean_dec(x_1367);
lean_dec(x_4);
x_1374 = lean_ctor_get(x_1371, 1);
lean_inc(x_1374);
lean_dec(x_1371);
x_1375 = lean_box(0);
if (lean_is_scalar(x_1369)) {
 x_1376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1376 = x_1369;
}
lean_ctor_set(x_1376, 0, x_1375);
lean_ctor_set(x_1376, 1, x_1368);
x_1115 = x_1376;
x_1116 = x_1374;
goto block_1133;
}
else
{
lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; 
lean_dec(x_1369);
x_1377 = lean_ctor_get(x_1371, 1);
lean_inc(x_1377);
lean_dec(x_1371);
x_1378 = l_Lean_Syntax_formatStxAux___main(x_155, x_156, x_1135, x_1367);
x_1379 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1379, 0, x_1378);
x_1380 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_1381 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1381, 0, x_1380);
lean_ctor_set(x_1381, 1, x_1379);
x_1382 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1370, x_1381, x_4, x_1368, x_6, x_1377);
lean_dec(x_4);
x_1383 = lean_ctor_get(x_1382, 0);
lean_inc(x_1383);
x_1384 = lean_ctor_get(x_1382, 1);
lean_inc(x_1384);
lean_dec(x_1382);
x_1115 = x_1383;
x_1116 = x_1384;
goto block_1133;
}
}
}
}
}
}
}
block_1436:
{
lean_object* x_1405; uint8_t x_1406; 
x_1405 = lean_ctor_get(x_1403, 0);
lean_inc(x_1405);
x_1406 = lean_unbox(x_1405);
lean_dec(x_1405);
if (x_1406 == 0)
{
lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; 
x_1407 = lean_ctor_get(x_1403, 1);
lean_inc(x_1407);
if (lean_is_exclusive(x_1403)) {
 lean_ctor_release(x_1403, 0);
 lean_ctor_release(x_1403, 1);
 x_1408 = x_1403;
} else {
 lean_dec_ref(x_1403);
 x_1408 = lean_box(0);
}
x_1409 = lean_box(0);
if (lean_is_scalar(x_1408)) {
 x_1410 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1410 = x_1408;
}
lean_ctor_set(x_1410, 0, x_1409);
lean_ctor_set(x_1410, 1, x_1407);
x_1111 = x_1410;
x_1112 = x_1404;
goto block_1402;
}
else
{
lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; 
x_1411 = lean_ctor_get(x_1403, 1);
lean_inc(x_1411);
lean_dec(x_1403);
lean_inc(x_2);
x_1412 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_2);
x_1413 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1413, 0, x_1412);
x_1414 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__17;
x_1415 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1415, 0, x_1414);
lean_ctor_set(x_1415, 1, x_1413);
x_1416 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__20;
x_1417 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1417, 0, x_1415);
lean_ctor_set(x_1417, 1, x_1416);
lean_inc(x_1110);
x_1418 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_1110);
x_1419 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1419, 0, x_1418);
x_1420 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1420, 0, x_1417);
lean_ctor_set(x_1420, 1, x_1419);
x_1421 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_1422 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1422, 0, x_1420);
lean_ctor_set(x_1422, 1, x_1421);
lean_inc(x_1109);
x_1423 = l_Lean_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_1109);
x_1424 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1424, 0, x_1423);
x_1425 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1425, 0, x_1422);
lean_ctor_set(x_1425, 1, x_1424);
x_1426 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__23;
x_1427 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1427, 0, x_1425);
lean_ctor_set(x_1427, 1, x_1426);
x_1428 = lean_ctor_get(x_18, 1);
lean_inc(x_1428);
x_1429 = l_Lean_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_1428);
x_1430 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1430, 0, x_1429);
x_1431 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1431, 0, x_1427);
lean_ctor_set(x_1431, 1, x_1430);
x_1432 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1433 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1432, x_1431, x_4, x_1411, x_6, x_1404);
x_1434 = lean_ctor_get(x_1433, 0);
lean_inc(x_1434);
x_1435 = lean_ctor_get(x_1433, 1);
lean_inc(x_1435);
lean_dec(x_1433);
x_1111 = x_1434;
x_1112 = x_1435;
goto block_1402;
}
}
}
}
}
else
{
uint8_t x_1446; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1446 = !lean_is_exclusive(x_162);
if (x_1446 == 0)
{
return x_162;
}
else
{
lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; 
x_1447 = lean_ctor_get(x_162, 0);
x_1448 = lean_ctor_get(x_162, 1);
lean_inc(x_1448);
lean_inc(x_1447);
lean_dec(x_162);
x_1449 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1449, 0, x_1447);
lean_ctor_set(x_1449, 1, x_1448);
return x_1449;
}
}
}
block_1492:
{
lean_object* x_1453; uint8_t x_1454; 
x_1453 = lean_ctor_get(x_1451, 0);
lean_inc(x_1453);
x_1454 = lean_unbox(x_1453);
lean_dec(x_1453);
if (x_1454 == 0)
{
uint8_t x_1455; 
lean_dec(x_11);
x_1455 = !lean_is_exclusive(x_1451);
if (x_1455 == 0)
{
lean_object* x_1456; lean_object* x_1457; 
x_1456 = lean_ctor_get(x_1451, 0);
lean_dec(x_1456);
x_1457 = lean_box(0);
lean_ctor_set(x_1451, 0, x_1457);
x_158 = x_1451;
x_159 = x_1452;
goto block_1450;
}
else
{
lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; 
x_1458 = lean_ctor_get(x_1451, 1);
lean_inc(x_1458);
lean_dec(x_1451);
x_1459 = lean_box(0);
x_1460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1460, 0, x_1459);
lean_ctor_set(x_1460, 1, x_1458);
x_158 = x_1460;
x_159 = x_1452;
goto block_1450;
}
}
else
{
lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; 
x_1461 = lean_ctor_get(x_1451, 1);
lean_inc(x_1461);
lean_dec(x_1451);
x_1462 = lean_ctor_get(x_18, 1);
lean_inc(x_1462);
x_1463 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1463, 0, x_11);
x_1464 = l_Lean_MessageData_ofList___closed__3;
x_1465 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1465, 0, x_1464);
lean_ctor_set(x_1465, 1, x_1463);
x_1466 = lean_unsigned_to_nat(2u);
x_1467 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1467, 0, x_1466);
lean_ctor_set(x_1467, 1, x_1465);
if (lean_obj_tag(x_1462) == 0)
{
lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; 
x_1468 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__29;
x_1469 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1469, 0, x_1468);
lean_ctor_set(x_1469, 1, x_1467);
x_1470 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1471 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1470, x_1469, x_4, x_1461, x_6, x_1452);
x_1472 = lean_ctor_get(x_1471, 0);
lean_inc(x_1472);
x_1473 = lean_ctor_get(x_1471, 1);
lean_inc(x_1473);
lean_dec(x_1471);
x_158 = x_1472;
x_159 = x_1473;
goto block_1450;
}
else
{
lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; 
x_1474 = lean_ctor_get(x_1462, 0);
lean_inc(x_1474);
lean_dec(x_1462);
x_1475 = l_Nat_repr(x_1474);
x_1476 = l_addParenHeuristic(x_1475);
lean_dec(x_1475);
x_1477 = l_Option_HasRepr___rarg___closed__2;
x_1478 = lean_string_append(x_1477, x_1476);
lean_dec(x_1476);
x_1479 = l_Option_HasRepr___rarg___closed__3;
x_1480 = lean_string_append(x_1478, x_1479);
x_1481 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1481, 0, x_1480);
x_1482 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1482, 0, x_1481);
x_1483 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__26;
x_1484 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1484, 0, x_1483);
lean_ctor_set(x_1484, 1, x_1482);
x_1485 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__27;
x_1486 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1486, 0, x_1484);
lean_ctor_set(x_1486, 1, x_1485);
x_1487 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1487, 0, x_1486);
lean_ctor_set(x_1487, 1, x_1467);
x_1488 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1489 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1488, x_1487, x_4, x_1461, x_6, x_1452);
x_1490 = lean_ctor_get(x_1489, 0);
lean_inc(x_1490);
x_1491 = lean_ctor_get(x_1489, 1);
lean_inc(x_1491);
lean_dec(x_1489);
x_158 = x_1490;
x_159 = x_1491;
goto block_1450;
}
}
}
}
else
{
lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1548; lean_object* x_1549; uint8_t x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1910; lean_object* x_1911; lean_object* x_1950; uint8_t x_1951; 
x_1500 = lean_ctor_get(x_14, 0);
x_1501 = lean_ctor_get(x_14, 1);
lean_inc(x_1501);
lean_inc(x_1500);
lean_dec(x_14);
x_1548 = lean_ctor_get(x_1501, 0);
lean_inc(x_1548);
x_1549 = lean_box(0);
x_1550 = 0;
x_1551 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_1551, 0, x_1548);
lean_ctor_set(x_1551, 1, x_1549);
lean_ctor_set(x_1551, 2, x_1549);
lean_ctor_set(x_1551, 3, x_1549);
lean_ctor_set_uint8(x_1551, sizeof(void*)*4, x_1550);
x_1950 = lean_ctor_get(x_15, 4);
lean_inc(x_1950);
x_1951 = lean_ctor_get_uint8(x_1950, sizeof(void*)*1);
lean_dec(x_1950);
if (x_1951 == 0)
{
lean_object* x_1952; lean_object* x_1953; 
x_1952 = lean_box(x_1550);
x_1953 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1953, 0, x_1952);
lean_ctor_set(x_1953, 1, x_1551);
x_1910 = x_1953;
x_1911 = x_15;
goto block_1949;
}
else
{
lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; lean_object* x_1957; lean_object* x_1958; 
x_1954 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1955 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1954, x_6, x_15);
x_1956 = lean_ctor_get(x_1955, 0);
lean_inc(x_1956);
x_1957 = lean_ctor_get(x_1955, 1);
lean_inc(x_1957);
lean_dec(x_1955);
x_1958 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1958, 0, x_1956);
lean_ctor_set(x_1958, 1, x_1551);
x_1910 = x_1958;
x_1911 = x_1957;
goto block_1949;
}
block_1547:
{
lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; uint8_t x_1506; 
x_1503 = lean_ctor_get(x_1502, 0);
lean_inc(x_1503);
x_1504 = lean_ctor_get(x_1503, 1);
lean_inc(x_1504);
if (lean_is_exclusive(x_1503)) {
 lean_ctor_release(x_1503, 0);
 lean_ctor_release(x_1503, 1);
 x_1505 = x_1503;
} else {
 lean_dec_ref(x_1503);
 x_1505 = lean_box(0);
}
x_1506 = lean_ctor_get_uint8(x_1501, sizeof(void*)*4);
if (x_1506 == 0)
{
lean_object* x_1507; 
x_1507 = lean_ctor_get(x_1504, 3);
lean_inc(x_1507);
if (lean_obj_tag(x_1507) == 0)
{
lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; uint8_t x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; 
x_1508 = lean_ctor_get(x_1502, 1);
lean_inc(x_1508);
if (lean_is_exclusive(x_1502)) {
 lean_ctor_release(x_1502, 0);
 lean_ctor_release(x_1502, 1);
 x_1509 = x_1502;
} else {
 lean_dec_ref(x_1502);
 x_1509 = lean_box(0);
}
x_1510 = lean_ctor_get(x_1504, 0);
lean_inc(x_1510);
x_1511 = lean_ctor_get(x_1504, 1);
lean_inc(x_1511);
x_1512 = lean_ctor_get_uint8(x_1504, sizeof(void*)*4);
lean_dec(x_1504);
x_1513 = lean_ctor_get(x_1501, 2);
lean_inc(x_1513);
if (lean_is_exclusive(x_1501)) {
 lean_ctor_release(x_1501, 0);
 lean_ctor_release(x_1501, 1);
 lean_ctor_release(x_1501, 2);
 lean_ctor_release(x_1501, 3);
 x_1514 = x_1501;
} else {
 lean_dec_ref(x_1501);
 x_1514 = lean_box(0);
}
x_1515 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1515, 0, x_2);
if (lean_is_scalar(x_1514)) {
 x_1516 = lean_alloc_ctor(0, 4, 1);
} else {
 x_1516 = x_1514;
}
lean_ctor_set(x_1516, 0, x_1510);
lean_ctor_set(x_1516, 1, x_1511);
lean_ctor_set(x_1516, 2, x_1513);
lean_ctor_set(x_1516, 3, x_1515);
lean_ctor_set_uint8(x_1516, sizeof(void*)*4, x_1512);
x_1517 = lean_box(0);
if (lean_is_scalar(x_1505)) {
 x_1518 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1518 = x_1505;
}
lean_ctor_set(x_1518, 0, x_1517);
lean_ctor_set(x_1518, 1, x_1516);
if (lean_is_scalar(x_1509)) {
 x_1519 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1519 = x_1509;
}
lean_ctor_set(x_1519, 0, x_1518);
lean_ctor_set(x_1519, 1, x_1508);
return x_1519;
}
else
{
lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; uint8_t x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; 
x_1520 = lean_ctor_get(x_1502, 1);
lean_inc(x_1520);
if (lean_is_exclusive(x_1502)) {
 lean_ctor_release(x_1502, 0);
 lean_ctor_release(x_1502, 1);
 x_1521 = x_1502;
} else {
 lean_dec_ref(x_1502);
 x_1521 = lean_box(0);
}
x_1522 = lean_ctor_get(x_1504, 0);
lean_inc(x_1522);
x_1523 = lean_ctor_get(x_1504, 1);
lean_inc(x_1523);
x_1524 = lean_ctor_get_uint8(x_1504, sizeof(void*)*4);
lean_dec(x_1504);
x_1525 = lean_ctor_get(x_1501, 2);
lean_inc(x_1525);
if (lean_is_exclusive(x_1501)) {
 lean_ctor_release(x_1501, 0);
 lean_ctor_release(x_1501, 1);
 lean_ctor_release(x_1501, 2);
 lean_ctor_release(x_1501, 3);
 x_1526 = x_1501;
} else {
 lean_dec_ref(x_1501);
 x_1526 = lean_box(0);
}
x_1527 = lean_ctor_get(x_1507, 0);
lean_inc(x_1527);
if (lean_is_exclusive(x_1507)) {
 lean_ctor_release(x_1507, 0);
 x_1528 = x_1507;
} else {
 lean_dec_ref(x_1507);
 x_1528 = lean_box(0);
}
x_1529 = l_Nat_min(x_1527, x_2);
lean_dec(x_2);
lean_dec(x_1527);
if (lean_is_scalar(x_1528)) {
 x_1530 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1530 = x_1528;
}
lean_ctor_set(x_1530, 0, x_1529);
if (lean_is_scalar(x_1526)) {
 x_1531 = lean_alloc_ctor(0, 4, 1);
} else {
 x_1531 = x_1526;
}
lean_ctor_set(x_1531, 0, x_1522);
lean_ctor_set(x_1531, 1, x_1523);
lean_ctor_set(x_1531, 2, x_1525);
lean_ctor_set(x_1531, 3, x_1530);
lean_ctor_set_uint8(x_1531, sizeof(void*)*4, x_1524);
x_1532 = lean_box(0);
if (lean_is_scalar(x_1505)) {
 x_1533 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1533 = x_1505;
}
lean_ctor_set(x_1533, 0, x_1532);
lean_ctor_set(x_1533, 1, x_1531);
if (lean_is_scalar(x_1521)) {
 x_1534 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1534 = x_1521;
}
lean_ctor_set(x_1534, 0, x_1533);
lean_ctor_set(x_1534, 1, x_1520);
return x_1534;
}
}
else
{
lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; uint8_t x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; 
lean_dec(x_2);
x_1535 = lean_ctor_get(x_1502, 1);
lean_inc(x_1535);
if (lean_is_exclusive(x_1502)) {
 lean_ctor_release(x_1502, 0);
 lean_ctor_release(x_1502, 1);
 x_1536 = x_1502;
} else {
 lean_dec_ref(x_1502);
 x_1536 = lean_box(0);
}
x_1537 = lean_ctor_get(x_1504, 0);
lean_inc(x_1537);
x_1538 = lean_ctor_get(x_1504, 1);
lean_inc(x_1538);
x_1539 = lean_ctor_get_uint8(x_1504, sizeof(void*)*4);
lean_dec(x_1504);
x_1540 = lean_ctor_get(x_1501, 2);
lean_inc(x_1540);
x_1541 = lean_ctor_get(x_1501, 3);
lean_inc(x_1541);
if (lean_is_exclusive(x_1501)) {
 lean_ctor_release(x_1501, 0);
 lean_ctor_release(x_1501, 1);
 lean_ctor_release(x_1501, 2);
 lean_ctor_release(x_1501, 3);
 x_1542 = x_1501;
} else {
 lean_dec_ref(x_1501);
 x_1542 = lean_box(0);
}
if (lean_is_scalar(x_1542)) {
 x_1543 = lean_alloc_ctor(0, 4, 1);
} else {
 x_1543 = x_1542;
}
lean_ctor_set(x_1543, 0, x_1537);
lean_ctor_set(x_1543, 1, x_1538);
lean_ctor_set(x_1543, 2, x_1540);
lean_ctor_set(x_1543, 3, x_1541);
lean_ctor_set_uint8(x_1543, sizeof(void*)*4, x_1539);
x_1544 = lean_box(0);
if (lean_is_scalar(x_1505)) {
 x_1545 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1545 = x_1505;
}
lean_ctor_set(x_1545, 0, x_1544);
lean_ctor_set(x_1545, 1, x_1543);
if (lean_is_scalar(x_1536)) {
 x_1546 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1546 = x_1536;
}
lean_ctor_set(x_1546, 0, x_1545);
lean_ctor_set(x_1546, 1, x_1535);
return x_1546;
}
}
block_1909:
{
lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; 
x_1554 = lean_ctor_get(x_1552, 1);
lean_inc(x_1554);
lean_dec(x_1552);
lean_inc(x_1);
x_1555 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1555, 0, x_1);
lean_inc(x_6);
x_1556 = lean_apply_4(x_3, x_1555, x_1554, x_6, x_1553);
if (lean_obj_tag(x_1556) == 0)
{
lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; 
x_1557 = lean_ctor_get(x_1556, 0);
lean_inc(x_1557);
x_1558 = lean_ctor_get(x_1557, 1);
lean_inc(x_1558);
if (lean_is_exclusive(x_1557)) {
 lean_ctor_release(x_1557, 0);
 lean_ctor_release(x_1557, 1);
 x_1559 = x_1557;
} else {
 lean_dec_ref(x_1557);
 x_1559 = lean_box(0);
}
x_1560 = lean_ctor_get(x_1558, 2);
lean_inc(x_1560);
if (lean_obj_tag(x_1560) == 0)
{
lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; 
lean_dec(x_1559);
lean_dec(x_1501);
lean_dec(x_1500);
lean_dec(x_2);
lean_dec(x_1);
x_1561 = lean_ctor_get(x_1556, 1);
lean_inc(x_1561);
lean_dec(x_1556);
x_1562 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6;
x_1563 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__9;
x_1564 = lean_panic_fn(x_1562, x_1563);
x_1565 = lean_apply_4(x_1564, x_4, x_1558, x_6, x_1561);
return x_1565;
}
else
{
lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1862; lean_object* x_1863; lean_object* x_1896; uint8_t x_1897; 
x_1566 = lean_ctor_get(x_1556, 1);
lean_inc(x_1566);
if (lean_is_exclusive(x_1556)) {
 lean_ctor_release(x_1556, 0);
 lean_ctor_release(x_1556, 1);
 x_1567 = x_1556;
} else {
 lean_dec_ref(x_1556);
 x_1567 = lean_box(0);
}
x_1568 = lean_ctor_get(x_1558, 3);
lean_inc(x_1568);
x_1569 = lean_ctor_get(x_1560, 0);
lean_inc(x_1569);
lean_dec(x_1560);
x_1896 = lean_ctor_get(x_1566, 4);
lean_inc(x_1896);
x_1897 = lean_ctor_get_uint8(x_1896, sizeof(void*)*1);
lean_dec(x_1896);
if (x_1897 == 0)
{
lean_object* x_1898; lean_object* x_1899; 
x_1898 = lean_box(x_1550);
if (lean_is_scalar(x_1559)) {
 x_1899 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1899 = x_1559;
}
lean_ctor_set(x_1899, 0, x_1898);
lean_ctor_set(x_1899, 1, x_1558);
x_1862 = x_1899;
x_1863 = x_1566;
goto block_1895;
}
else
{
lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; 
x_1900 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1901 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1900, x_6, x_1566);
x_1902 = lean_ctor_get(x_1901, 0);
lean_inc(x_1902);
x_1903 = lean_ctor_get(x_1901, 1);
lean_inc(x_1903);
lean_dec(x_1901);
if (lean_is_scalar(x_1559)) {
 x_1904 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1904 = x_1559;
}
lean_ctor_set(x_1904, 0, x_1902);
lean_ctor_set(x_1904, 1, x_1558);
x_1862 = x_1904;
x_1863 = x_1903;
goto block_1895;
}
block_1861:
{
lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1593; uint8_t x_1845; 
x_1572 = lean_ctor_get(x_1570, 1);
lean_inc(x_1572);
if (lean_is_exclusive(x_1570)) {
 lean_ctor_release(x_1570, 0);
 lean_ctor_release(x_1570, 1);
 x_1573 = x_1570;
} else {
 lean_dec_ref(x_1570);
 x_1573 = lean_box(0);
}
x_1845 = lean_nat_dec_lt(x_1569, x_2);
lean_dec(x_1569);
if (x_1845 == 0)
{
if (lean_obj_tag(x_1568) == 0)
{
lean_object* x_1846; lean_object* x_1847; lean_object* x_1848; 
lean_dec(x_1500);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_1846 = lean_box(0);
if (lean_is_scalar(x_1573)) {
 x_1847 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1847 = x_1573;
}
lean_ctor_set(x_1847, 0, x_1846);
lean_ctor_set(x_1847, 1, x_1572);
if (lean_is_scalar(x_1567)) {
 x_1848 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1848 = x_1567;
}
lean_ctor_set(x_1848, 0, x_1847);
lean_ctor_set(x_1848, 1, x_1571);
x_1502 = x_1848;
goto block_1547;
}
else
{
lean_object* x_1849; 
x_1849 = lean_ctor_get(x_1501, 1);
lean_inc(x_1849);
if (lean_obj_tag(x_1849) == 0)
{
lean_object* x_1850; lean_object* x_1851; lean_object* x_1852; 
lean_dec(x_1568);
lean_dec(x_1500);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_1850 = lean_box(0);
if (lean_is_scalar(x_1573)) {
 x_1851 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1851 = x_1573;
}
lean_ctor_set(x_1851, 0, x_1850);
lean_ctor_set(x_1851, 1, x_1572);
if (lean_is_scalar(x_1567)) {
 x_1852 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1852 = x_1567;
}
lean_ctor_set(x_1852, 0, x_1851);
lean_ctor_set(x_1852, 1, x_1571);
x_1502 = x_1852;
goto block_1547;
}
else
{
lean_object* x_1853; lean_object* x_1854; uint8_t x_1855; 
x_1853 = lean_ctor_get(x_1568, 0);
lean_inc(x_1853);
lean_dec(x_1568);
x_1854 = lean_ctor_get(x_1849, 0);
lean_inc(x_1854);
lean_dec(x_1849);
x_1855 = lean_nat_dec_le(x_1853, x_1854);
lean_dec(x_1854);
lean_dec(x_1853);
if (x_1855 == 0)
{
lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; 
lean_dec(x_1500);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_1856 = lean_box(0);
if (lean_is_scalar(x_1573)) {
 x_1857 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1857 = x_1573;
}
lean_ctor_set(x_1857, 0, x_1856);
lean_ctor_set(x_1857, 1, x_1572);
if (lean_is_scalar(x_1567)) {
 x_1858 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1858 = x_1567;
}
lean_ctor_set(x_1858, 0, x_1857);
lean_ctor_set(x_1858, 1, x_1571);
x_1502 = x_1858;
goto block_1547;
}
else
{
lean_object* x_1859; 
lean_dec(x_1573);
lean_dec(x_1567);
x_1859 = lean_box(0);
x_1593 = x_1859;
goto block_1844;
}
}
}
}
else
{
lean_object* x_1860; 
lean_dec(x_1573);
lean_dec(x_1568);
lean_dec(x_1567);
x_1860 = lean_box(0);
x_1593 = x_1860;
goto block_1844;
}
block_1592:
{
lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; uint8_t x_1585; lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; 
x_1576 = lean_ctor_get(x_1574, 1);
lean_inc(x_1576);
lean_dec(x_1574);
x_1577 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_1576, x_6, x_1575);
lean_dec(x_6);
x_1578 = lean_ctor_get(x_1577, 0);
lean_inc(x_1578);
x_1579 = lean_ctor_get(x_1578, 1);
lean_inc(x_1579);
if (lean_is_exclusive(x_1578)) {
 lean_ctor_release(x_1578, 0);
 lean_ctor_release(x_1578, 1);
 x_1580 = x_1578;
} else {
 lean_dec_ref(x_1578);
 x_1580 = lean_box(0);
}
x_1581 = lean_ctor_get(x_1577, 1);
lean_inc(x_1581);
if (lean_is_exclusive(x_1577)) {
 lean_ctor_release(x_1577, 0);
 lean_ctor_release(x_1577, 1);
 x_1582 = x_1577;
} else {
 lean_dec_ref(x_1577);
 x_1582 = lean_box(0);
}
x_1583 = lean_ctor_get(x_1579, 0);
lean_inc(x_1583);
x_1584 = lean_ctor_get(x_1579, 2);
lean_inc(x_1584);
x_1585 = lean_ctor_get_uint8(x_1579, sizeof(void*)*4);
if (lean_is_exclusive(x_1579)) {
 lean_ctor_release(x_1579, 0);
 lean_ctor_release(x_1579, 1);
 lean_ctor_release(x_1579, 2);
 lean_ctor_release(x_1579, 3);
 x_1586 = x_1579;
} else {
 lean_dec_ref(x_1579);
 x_1586 = lean_box(0);
}
x_1587 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
if (lean_is_scalar(x_1586)) {
 x_1588 = lean_alloc_ctor(0, 4, 1);
} else {
 x_1588 = x_1586;
}
lean_ctor_set(x_1588, 0, x_1583);
lean_ctor_set(x_1588, 1, x_1587);
lean_ctor_set(x_1588, 2, x_1584);
lean_ctor_set(x_1588, 3, x_1549);
lean_ctor_set_uint8(x_1588, sizeof(void*)*4, x_1585);
x_1589 = lean_box(0);
if (lean_is_scalar(x_1580)) {
 x_1590 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1590 = x_1580;
}
lean_ctor_set(x_1590, 0, x_1589);
lean_ctor_set(x_1590, 1, x_1588);
if (lean_is_scalar(x_1582)) {
 x_1591 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1591 = x_1582;
}
lean_ctor_set(x_1591, 0, x_1590);
lean_ctor_set(x_1591, 1, x_1581);
x_1502 = x_1591;
goto block_1547;
}
block_1844:
{
lean_object* x_1594; uint8_t x_1595; 
lean_dec(x_1593);
x_1594 = lean_unsigned_to_nat(0u);
x_1595 = lean_nat_dec_lt(x_1594, x_1500);
lean_dec(x_1500);
if (x_1595 == 0)
{
lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; 
x_1596 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_1572, x_6, x_1571);
x_1597 = lean_ctor_get(x_1596, 0);
lean_inc(x_1597);
x_1598 = lean_ctor_get(x_1596, 1);
lean_inc(x_1598);
lean_dec(x_1596);
x_1599 = lean_ctor_get(x_1597, 0);
lean_inc(x_1599);
x_1600 = lean_ctor_get(x_1597, 1);
lean_inc(x_1600);
lean_dec(x_1597);
x_1601 = l_Lean_Syntax_getHeadInfo___main(x_1599);
if (lean_obj_tag(x_1601) == 0)
{
lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; uint8_t x_1611; 
x_1602 = lean_apply_1(x_1, x_1599);
x_1603 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_1602, x_4, x_1600, x_6, x_1598);
x_1604 = lean_ctor_get(x_1603, 0);
lean_inc(x_1604);
x_1605 = lean_ctor_get(x_1603, 1);
lean_inc(x_1605);
lean_dec(x_1603);
x_1606 = lean_ctor_get(x_1604, 1);
lean_inc(x_1606);
lean_dec(x_1604);
x_1607 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_1606, x_6, x_1605);
x_1608 = lean_ctor_get(x_1607, 0);
lean_inc(x_1608);
x_1609 = lean_ctor_get(x_1607, 1);
lean_inc(x_1609);
lean_dec(x_1607);
x_1610 = lean_ctor_get(x_1609, 4);
lean_inc(x_1610);
x_1611 = lean_ctor_get_uint8(x_1610, sizeof(void*)*1);
lean_dec(x_1610);
if (x_1611 == 0)
{
lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; 
lean_dec(x_4);
x_1612 = lean_ctor_get(x_1608, 1);
lean_inc(x_1612);
if (lean_is_exclusive(x_1608)) {
 lean_ctor_release(x_1608, 0);
 lean_ctor_release(x_1608, 1);
 x_1613 = x_1608;
} else {
 lean_dec_ref(x_1608);
 x_1613 = lean_box(0);
}
x_1614 = lean_box(0);
if (lean_is_scalar(x_1613)) {
 x_1615 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1615 = x_1613;
}
lean_ctor_set(x_1615, 0, x_1614);
lean_ctor_set(x_1615, 1, x_1612);
x_1574 = x_1615;
x_1575 = x_1609;
goto block_1592;
}
else
{
lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; uint8_t x_1622; 
x_1616 = lean_ctor_get(x_1608, 0);
lean_inc(x_1616);
x_1617 = lean_ctor_get(x_1608, 1);
lean_inc(x_1617);
if (lean_is_exclusive(x_1608)) {
 lean_ctor_release(x_1608, 0);
 lean_ctor_release(x_1608, 1);
 x_1618 = x_1608;
} else {
 lean_dec_ref(x_1608);
 x_1618 = lean_box(0);
}
x_1619 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1620 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1619, x_6, x_1609);
x_1621 = lean_ctor_get(x_1620, 0);
lean_inc(x_1621);
x_1622 = lean_unbox(x_1621);
lean_dec(x_1621);
if (x_1622 == 0)
{
lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; 
lean_dec(x_1616);
lean_dec(x_4);
x_1623 = lean_ctor_get(x_1620, 1);
lean_inc(x_1623);
lean_dec(x_1620);
x_1624 = lean_box(0);
if (lean_is_scalar(x_1618)) {
 x_1625 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1625 = x_1618;
}
lean_ctor_set(x_1625, 0, x_1624);
lean_ctor_set(x_1625, 1, x_1617);
x_1574 = x_1625;
x_1575 = x_1623;
goto block_1592;
}
else
{
lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; 
lean_dec(x_1618);
x_1626 = lean_ctor_get(x_1620, 1);
lean_inc(x_1626);
lean_dec(x_1620);
x_1627 = l_Lean_Syntax_formatStxAux___main(x_1549, x_1550, x_1594, x_1616);
x_1628 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1628, 0, x_1627);
x_1629 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_1630 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1630, 0, x_1629);
lean_ctor_set(x_1630, 1, x_1628);
x_1631 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1619, x_1630, x_4, x_1617, x_6, x_1626);
lean_dec(x_4);
x_1632 = lean_ctor_get(x_1631, 0);
lean_inc(x_1632);
x_1633 = lean_ctor_get(x_1631, 1);
lean_inc(x_1633);
lean_dec(x_1631);
x_1574 = x_1632;
x_1575 = x_1633;
goto block_1592;
}
}
}
else
{
lean_object* x_1634; lean_object* x_1635; 
x_1634 = lean_ctor_get(x_1601, 0);
lean_inc(x_1634);
lean_dec(x_1601);
x_1635 = l_Lean_Syntax_getTailInfo___main(x_1599);
if (lean_obj_tag(x_1635) == 0)
{
lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; uint8_t x_1645; 
lean_dec(x_1634);
x_1636 = lean_apply_1(x_1, x_1599);
x_1637 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_1636, x_4, x_1600, x_6, x_1598);
x_1638 = lean_ctor_get(x_1637, 0);
lean_inc(x_1638);
x_1639 = lean_ctor_get(x_1637, 1);
lean_inc(x_1639);
lean_dec(x_1637);
x_1640 = lean_ctor_get(x_1638, 1);
lean_inc(x_1640);
lean_dec(x_1638);
x_1641 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_1640, x_6, x_1639);
x_1642 = lean_ctor_get(x_1641, 0);
lean_inc(x_1642);
x_1643 = lean_ctor_get(x_1641, 1);
lean_inc(x_1643);
lean_dec(x_1641);
x_1644 = lean_ctor_get(x_1643, 4);
lean_inc(x_1644);
x_1645 = lean_ctor_get_uint8(x_1644, sizeof(void*)*1);
lean_dec(x_1644);
if (x_1645 == 0)
{
lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; 
lean_dec(x_4);
x_1646 = lean_ctor_get(x_1642, 1);
lean_inc(x_1646);
if (lean_is_exclusive(x_1642)) {
 lean_ctor_release(x_1642, 0);
 lean_ctor_release(x_1642, 1);
 x_1647 = x_1642;
} else {
 lean_dec_ref(x_1642);
 x_1647 = lean_box(0);
}
x_1648 = lean_box(0);
if (lean_is_scalar(x_1647)) {
 x_1649 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1649 = x_1647;
}
lean_ctor_set(x_1649, 0, x_1648);
lean_ctor_set(x_1649, 1, x_1646);
x_1574 = x_1649;
x_1575 = x_1643;
goto block_1592;
}
else
{
lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; uint8_t x_1656; 
x_1650 = lean_ctor_get(x_1642, 0);
lean_inc(x_1650);
x_1651 = lean_ctor_get(x_1642, 1);
lean_inc(x_1651);
if (lean_is_exclusive(x_1642)) {
 lean_ctor_release(x_1642, 0);
 lean_ctor_release(x_1642, 1);
 x_1652 = x_1642;
} else {
 lean_dec_ref(x_1642);
 x_1652 = lean_box(0);
}
x_1653 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1654 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1653, x_6, x_1643);
x_1655 = lean_ctor_get(x_1654, 0);
lean_inc(x_1655);
x_1656 = lean_unbox(x_1655);
lean_dec(x_1655);
if (x_1656 == 0)
{
lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; 
lean_dec(x_1650);
lean_dec(x_4);
x_1657 = lean_ctor_get(x_1654, 1);
lean_inc(x_1657);
lean_dec(x_1654);
x_1658 = lean_box(0);
if (lean_is_scalar(x_1652)) {
 x_1659 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1659 = x_1652;
}
lean_ctor_set(x_1659, 0, x_1658);
lean_ctor_set(x_1659, 1, x_1651);
x_1574 = x_1659;
x_1575 = x_1657;
goto block_1592;
}
else
{
lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; 
lean_dec(x_1652);
x_1660 = lean_ctor_get(x_1654, 1);
lean_inc(x_1660);
lean_dec(x_1654);
x_1661 = l_Lean_Syntax_formatStxAux___main(x_1549, x_1550, x_1594, x_1650);
x_1662 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1662, 0, x_1661);
x_1663 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_1664 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1664, 0, x_1663);
lean_ctor_set(x_1664, 1, x_1662);
x_1665 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1653, x_1664, x_4, x_1651, x_6, x_1660);
lean_dec(x_4);
x_1666 = lean_ctor_get(x_1665, 0);
lean_inc(x_1666);
x_1667 = lean_ctor_get(x_1665, 1);
lean_inc(x_1667);
lean_dec(x_1665);
x_1574 = x_1666;
x_1575 = x_1667;
goto block_1592;
}
}
}
else
{
lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; uint8_t x_1695; 
x_1668 = lean_ctor_get(x_1635, 0);
lean_inc(x_1668);
lean_dec(x_1635);
x_1669 = lean_ctor_get(x_1634, 0);
lean_inc(x_1669);
x_1670 = lean_ctor_get(x_1634, 1);
lean_inc(x_1670);
x_1671 = lean_ctor_get(x_1634, 2);
lean_inc(x_1671);
if (lean_is_exclusive(x_1634)) {
 lean_ctor_release(x_1634, 0);
 lean_ctor_release(x_1634, 1);
 lean_ctor_release(x_1634, 2);
 x_1672 = x_1634;
} else {
 lean_dec_ref(x_1634);
 x_1672 = lean_box(0);
}
x_1673 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14;
lean_inc(x_1670);
if (lean_is_scalar(x_1672)) {
 x_1674 = lean_alloc_ctor(0, 3, 0);
} else {
 x_1674 = x_1672;
}
lean_ctor_set(x_1674, 0, x_1673);
lean_ctor_set(x_1674, 1, x_1670);
lean_ctor_set(x_1674, 2, x_1671);
x_1675 = l_Lean_Syntax_setHeadInfo(x_1599, x_1674);
x_1676 = lean_ctor_get(x_1668, 0);
lean_inc(x_1676);
x_1677 = lean_ctor_get(x_1668, 1);
lean_inc(x_1677);
x_1678 = lean_ctor_get(x_1668, 2);
lean_inc(x_1678);
if (lean_is_exclusive(x_1668)) {
 lean_ctor_release(x_1668, 0);
 lean_ctor_release(x_1668, 1);
 lean_ctor_release(x_1668, 2);
 x_1679 = x_1668;
} else {
 lean_dec_ref(x_1668);
 x_1679 = lean_box(0);
}
lean_inc(x_1677);
if (lean_is_scalar(x_1679)) {
 x_1680 = lean_alloc_ctor(0, 3, 0);
} else {
 x_1680 = x_1679;
}
lean_ctor_set(x_1680, 0, x_1676);
lean_ctor_set(x_1680, 1, x_1677);
lean_ctor_set(x_1680, 2, x_1673);
x_1681 = l_Lean_Syntax_setTailInfo(x_1675, x_1680);
x_1682 = lean_apply_1(x_1, x_1681);
x_1683 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1683, 0, x_1669);
lean_ctor_set(x_1683, 1, x_1670);
lean_ctor_set(x_1683, 2, x_1673);
x_1684 = l_Lean_Syntax_setHeadInfo(x_1682, x_1683);
x_1685 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1685, 0, x_1673);
lean_ctor_set(x_1685, 1, x_1677);
lean_ctor_set(x_1685, 2, x_1678);
x_1686 = l_Lean_Syntax_setTailInfo(x_1684, x_1685);
x_1687 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_1686, x_4, x_1600, x_6, x_1598);
x_1688 = lean_ctor_get(x_1687, 0);
lean_inc(x_1688);
x_1689 = lean_ctor_get(x_1687, 1);
lean_inc(x_1689);
lean_dec(x_1687);
x_1690 = lean_ctor_get(x_1688, 1);
lean_inc(x_1690);
lean_dec(x_1688);
x_1691 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_1690, x_6, x_1689);
x_1692 = lean_ctor_get(x_1691, 0);
lean_inc(x_1692);
x_1693 = lean_ctor_get(x_1691, 1);
lean_inc(x_1693);
lean_dec(x_1691);
x_1694 = lean_ctor_get(x_1693, 4);
lean_inc(x_1694);
x_1695 = lean_ctor_get_uint8(x_1694, sizeof(void*)*1);
lean_dec(x_1694);
if (x_1695 == 0)
{
lean_object* x_1696; lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; 
lean_dec(x_4);
x_1696 = lean_ctor_get(x_1692, 1);
lean_inc(x_1696);
if (lean_is_exclusive(x_1692)) {
 lean_ctor_release(x_1692, 0);
 lean_ctor_release(x_1692, 1);
 x_1697 = x_1692;
} else {
 lean_dec_ref(x_1692);
 x_1697 = lean_box(0);
}
x_1698 = lean_box(0);
if (lean_is_scalar(x_1697)) {
 x_1699 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1699 = x_1697;
}
lean_ctor_set(x_1699, 0, x_1698);
lean_ctor_set(x_1699, 1, x_1696);
x_1574 = x_1699;
x_1575 = x_1693;
goto block_1592;
}
else
{
lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; uint8_t x_1706; 
x_1700 = lean_ctor_get(x_1692, 0);
lean_inc(x_1700);
x_1701 = lean_ctor_get(x_1692, 1);
lean_inc(x_1701);
if (lean_is_exclusive(x_1692)) {
 lean_ctor_release(x_1692, 0);
 lean_ctor_release(x_1692, 1);
 x_1702 = x_1692;
} else {
 lean_dec_ref(x_1692);
 x_1702 = lean_box(0);
}
x_1703 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1704 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1703, x_6, x_1693);
x_1705 = lean_ctor_get(x_1704, 0);
lean_inc(x_1705);
x_1706 = lean_unbox(x_1705);
lean_dec(x_1705);
if (x_1706 == 0)
{
lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; 
lean_dec(x_1700);
lean_dec(x_4);
x_1707 = lean_ctor_get(x_1704, 1);
lean_inc(x_1707);
lean_dec(x_1704);
x_1708 = lean_box(0);
if (lean_is_scalar(x_1702)) {
 x_1709 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1709 = x_1702;
}
lean_ctor_set(x_1709, 0, x_1708);
lean_ctor_set(x_1709, 1, x_1701);
x_1574 = x_1709;
x_1575 = x_1707;
goto block_1592;
}
else
{
lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; 
lean_dec(x_1702);
x_1710 = lean_ctor_get(x_1704, 1);
lean_inc(x_1710);
lean_dec(x_1704);
x_1711 = l_Lean_Syntax_formatStxAux___main(x_1549, x_1550, x_1594, x_1700);
x_1712 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1712, 0, x_1711);
x_1713 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_1714 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1714, 0, x_1713);
lean_ctor_set(x_1714, 1, x_1712);
x_1715 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1703, x_1714, x_4, x_1701, x_6, x_1710);
lean_dec(x_4);
x_1716 = lean_ctor_get(x_1715, 0);
lean_inc(x_1716);
x_1717 = lean_ctor_get(x_1715, 1);
lean_inc(x_1717);
lean_dec(x_1715);
x_1574 = x_1716;
x_1575 = x_1717;
goto block_1592;
}
}
}
}
}
else
{
lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; 
x_1718 = l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___rarg(x_1572, x_6, x_1571);
x_1719 = lean_ctor_get(x_1718, 0);
lean_inc(x_1719);
x_1720 = lean_ctor_get(x_1718, 1);
lean_inc(x_1720);
lean_dec(x_1718);
x_1721 = lean_ctor_get(x_1719, 1);
lean_inc(x_1721);
lean_dec(x_1719);
x_1722 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_1721, x_6, x_1720);
x_1723 = lean_ctor_get(x_1722, 0);
lean_inc(x_1723);
x_1724 = lean_ctor_get(x_1722, 1);
lean_inc(x_1724);
lean_dec(x_1722);
x_1725 = lean_ctor_get(x_1723, 0);
lean_inc(x_1725);
x_1726 = lean_ctor_get(x_1723, 1);
lean_inc(x_1726);
lean_dec(x_1723);
x_1727 = l_Lean_Syntax_getHeadInfo___main(x_1725);
if (lean_obj_tag(x_1727) == 0)
{
lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; uint8_t x_1737; 
x_1728 = lean_apply_1(x_1, x_1725);
x_1729 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_1728, x_4, x_1726, x_6, x_1724);
x_1730 = lean_ctor_get(x_1729, 0);
lean_inc(x_1730);
x_1731 = lean_ctor_get(x_1729, 1);
lean_inc(x_1731);
lean_dec(x_1729);
x_1732 = lean_ctor_get(x_1730, 1);
lean_inc(x_1732);
lean_dec(x_1730);
x_1733 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_1732, x_6, x_1731);
x_1734 = lean_ctor_get(x_1733, 0);
lean_inc(x_1734);
x_1735 = lean_ctor_get(x_1733, 1);
lean_inc(x_1735);
lean_dec(x_1733);
x_1736 = lean_ctor_get(x_1735, 4);
lean_inc(x_1736);
x_1737 = lean_ctor_get_uint8(x_1736, sizeof(void*)*1);
lean_dec(x_1736);
if (x_1737 == 0)
{
lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; 
lean_dec(x_4);
x_1738 = lean_ctor_get(x_1734, 1);
lean_inc(x_1738);
if (lean_is_exclusive(x_1734)) {
 lean_ctor_release(x_1734, 0);
 lean_ctor_release(x_1734, 1);
 x_1739 = x_1734;
} else {
 lean_dec_ref(x_1734);
 x_1739 = lean_box(0);
}
x_1740 = lean_box(0);
if (lean_is_scalar(x_1739)) {
 x_1741 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1741 = x_1739;
}
lean_ctor_set(x_1741, 0, x_1740);
lean_ctor_set(x_1741, 1, x_1738);
x_1574 = x_1741;
x_1575 = x_1735;
goto block_1592;
}
else
{
lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; uint8_t x_1748; 
x_1742 = lean_ctor_get(x_1734, 0);
lean_inc(x_1742);
x_1743 = lean_ctor_get(x_1734, 1);
lean_inc(x_1743);
if (lean_is_exclusive(x_1734)) {
 lean_ctor_release(x_1734, 0);
 lean_ctor_release(x_1734, 1);
 x_1744 = x_1734;
} else {
 lean_dec_ref(x_1734);
 x_1744 = lean_box(0);
}
x_1745 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1746 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1745, x_6, x_1735);
x_1747 = lean_ctor_get(x_1746, 0);
lean_inc(x_1747);
x_1748 = lean_unbox(x_1747);
lean_dec(x_1747);
if (x_1748 == 0)
{
lean_object* x_1749; lean_object* x_1750; lean_object* x_1751; 
lean_dec(x_1742);
lean_dec(x_4);
x_1749 = lean_ctor_get(x_1746, 1);
lean_inc(x_1749);
lean_dec(x_1746);
x_1750 = lean_box(0);
if (lean_is_scalar(x_1744)) {
 x_1751 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1751 = x_1744;
}
lean_ctor_set(x_1751, 0, x_1750);
lean_ctor_set(x_1751, 1, x_1743);
x_1574 = x_1751;
x_1575 = x_1749;
goto block_1592;
}
else
{
lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; 
lean_dec(x_1744);
x_1752 = lean_ctor_get(x_1746, 1);
lean_inc(x_1752);
lean_dec(x_1746);
x_1753 = l_Lean_Syntax_formatStxAux___main(x_1549, x_1550, x_1594, x_1742);
x_1754 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1754, 0, x_1753);
x_1755 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_1756 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1756, 0, x_1755);
lean_ctor_set(x_1756, 1, x_1754);
x_1757 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1745, x_1756, x_4, x_1743, x_6, x_1752);
lean_dec(x_4);
x_1758 = lean_ctor_get(x_1757, 0);
lean_inc(x_1758);
x_1759 = lean_ctor_get(x_1757, 1);
lean_inc(x_1759);
lean_dec(x_1757);
x_1574 = x_1758;
x_1575 = x_1759;
goto block_1592;
}
}
}
else
{
lean_object* x_1760; lean_object* x_1761; 
x_1760 = lean_ctor_get(x_1727, 0);
lean_inc(x_1760);
lean_dec(x_1727);
x_1761 = l_Lean_Syntax_getTailInfo___main(x_1725);
if (lean_obj_tag(x_1761) == 0)
{
lean_object* x_1762; lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; uint8_t x_1771; 
lean_dec(x_1760);
x_1762 = lean_apply_1(x_1, x_1725);
x_1763 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_1762, x_4, x_1726, x_6, x_1724);
x_1764 = lean_ctor_get(x_1763, 0);
lean_inc(x_1764);
x_1765 = lean_ctor_get(x_1763, 1);
lean_inc(x_1765);
lean_dec(x_1763);
x_1766 = lean_ctor_get(x_1764, 1);
lean_inc(x_1766);
lean_dec(x_1764);
x_1767 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_1766, x_6, x_1765);
x_1768 = lean_ctor_get(x_1767, 0);
lean_inc(x_1768);
x_1769 = lean_ctor_get(x_1767, 1);
lean_inc(x_1769);
lean_dec(x_1767);
x_1770 = lean_ctor_get(x_1769, 4);
lean_inc(x_1770);
x_1771 = lean_ctor_get_uint8(x_1770, sizeof(void*)*1);
lean_dec(x_1770);
if (x_1771 == 0)
{
lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; 
lean_dec(x_4);
x_1772 = lean_ctor_get(x_1768, 1);
lean_inc(x_1772);
if (lean_is_exclusive(x_1768)) {
 lean_ctor_release(x_1768, 0);
 lean_ctor_release(x_1768, 1);
 x_1773 = x_1768;
} else {
 lean_dec_ref(x_1768);
 x_1773 = lean_box(0);
}
x_1774 = lean_box(0);
if (lean_is_scalar(x_1773)) {
 x_1775 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1775 = x_1773;
}
lean_ctor_set(x_1775, 0, x_1774);
lean_ctor_set(x_1775, 1, x_1772);
x_1574 = x_1775;
x_1575 = x_1769;
goto block_1592;
}
else
{
lean_object* x_1776; lean_object* x_1777; lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; uint8_t x_1782; 
x_1776 = lean_ctor_get(x_1768, 0);
lean_inc(x_1776);
x_1777 = lean_ctor_get(x_1768, 1);
lean_inc(x_1777);
if (lean_is_exclusive(x_1768)) {
 lean_ctor_release(x_1768, 0);
 lean_ctor_release(x_1768, 1);
 x_1778 = x_1768;
} else {
 lean_dec_ref(x_1768);
 x_1778 = lean_box(0);
}
x_1779 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1780 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1779, x_6, x_1769);
x_1781 = lean_ctor_get(x_1780, 0);
lean_inc(x_1781);
x_1782 = lean_unbox(x_1781);
lean_dec(x_1781);
if (x_1782 == 0)
{
lean_object* x_1783; lean_object* x_1784; lean_object* x_1785; 
lean_dec(x_1776);
lean_dec(x_4);
x_1783 = lean_ctor_get(x_1780, 1);
lean_inc(x_1783);
lean_dec(x_1780);
x_1784 = lean_box(0);
if (lean_is_scalar(x_1778)) {
 x_1785 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1785 = x_1778;
}
lean_ctor_set(x_1785, 0, x_1784);
lean_ctor_set(x_1785, 1, x_1777);
x_1574 = x_1785;
x_1575 = x_1783;
goto block_1592;
}
else
{
lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; lean_object* x_1793; 
lean_dec(x_1778);
x_1786 = lean_ctor_get(x_1780, 1);
lean_inc(x_1786);
lean_dec(x_1780);
x_1787 = l_Lean_Syntax_formatStxAux___main(x_1549, x_1550, x_1594, x_1776);
x_1788 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1788, 0, x_1787);
x_1789 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_1790 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1790, 0, x_1789);
lean_ctor_set(x_1790, 1, x_1788);
x_1791 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1779, x_1790, x_4, x_1777, x_6, x_1786);
lean_dec(x_4);
x_1792 = lean_ctor_get(x_1791, 0);
lean_inc(x_1792);
x_1793 = lean_ctor_get(x_1791, 1);
lean_inc(x_1793);
lean_dec(x_1791);
x_1574 = x_1792;
x_1575 = x_1793;
goto block_1592;
}
}
}
else
{
lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; lean_object* x_1814; lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; lean_object* x_1820; uint8_t x_1821; 
x_1794 = lean_ctor_get(x_1761, 0);
lean_inc(x_1794);
lean_dec(x_1761);
x_1795 = lean_ctor_get(x_1760, 0);
lean_inc(x_1795);
x_1796 = lean_ctor_get(x_1760, 1);
lean_inc(x_1796);
x_1797 = lean_ctor_get(x_1760, 2);
lean_inc(x_1797);
if (lean_is_exclusive(x_1760)) {
 lean_ctor_release(x_1760, 0);
 lean_ctor_release(x_1760, 1);
 lean_ctor_release(x_1760, 2);
 x_1798 = x_1760;
} else {
 lean_dec_ref(x_1760);
 x_1798 = lean_box(0);
}
x_1799 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14;
lean_inc(x_1796);
if (lean_is_scalar(x_1798)) {
 x_1800 = lean_alloc_ctor(0, 3, 0);
} else {
 x_1800 = x_1798;
}
lean_ctor_set(x_1800, 0, x_1799);
lean_ctor_set(x_1800, 1, x_1796);
lean_ctor_set(x_1800, 2, x_1797);
x_1801 = l_Lean_Syntax_setHeadInfo(x_1725, x_1800);
x_1802 = lean_ctor_get(x_1794, 0);
lean_inc(x_1802);
x_1803 = lean_ctor_get(x_1794, 1);
lean_inc(x_1803);
x_1804 = lean_ctor_get(x_1794, 2);
lean_inc(x_1804);
if (lean_is_exclusive(x_1794)) {
 lean_ctor_release(x_1794, 0);
 lean_ctor_release(x_1794, 1);
 lean_ctor_release(x_1794, 2);
 x_1805 = x_1794;
} else {
 lean_dec_ref(x_1794);
 x_1805 = lean_box(0);
}
lean_inc(x_1803);
if (lean_is_scalar(x_1805)) {
 x_1806 = lean_alloc_ctor(0, 3, 0);
} else {
 x_1806 = x_1805;
}
lean_ctor_set(x_1806, 0, x_1802);
lean_ctor_set(x_1806, 1, x_1803);
lean_ctor_set(x_1806, 2, x_1799);
x_1807 = l_Lean_Syntax_setTailInfo(x_1801, x_1806);
x_1808 = lean_apply_1(x_1, x_1807);
x_1809 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1809, 0, x_1795);
lean_ctor_set(x_1809, 1, x_1796);
lean_ctor_set(x_1809, 2, x_1799);
x_1810 = l_Lean_Syntax_setHeadInfo(x_1808, x_1809);
x_1811 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1811, 0, x_1799);
lean_ctor_set(x_1811, 1, x_1803);
lean_ctor_set(x_1811, 2, x_1804);
x_1812 = l_Lean_Syntax_setTailInfo(x_1810, x_1811);
x_1813 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_1812, x_4, x_1726, x_6, x_1724);
x_1814 = lean_ctor_get(x_1813, 0);
lean_inc(x_1814);
x_1815 = lean_ctor_get(x_1813, 1);
lean_inc(x_1815);
lean_dec(x_1813);
x_1816 = lean_ctor_get(x_1814, 1);
lean_inc(x_1816);
lean_dec(x_1814);
x_1817 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_1816, x_6, x_1815);
x_1818 = lean_ctor_get(x_1817, 0);
lean_inc(x_1818);
x_1819 = lean_ctor_get(x_1817, 1);
lean_inc(x_1819);
lean_dec(x_1817);
x_1820 = lean_ctor_get(x_1819, 4);
lean_inc(x_1820);
x_1821 = lean_ctor_get_uint8(x_1820, sizeof(void*)*1);
lean_dec(x_1820);
if (x_1821 == 0)
{
lean_object* x_1822; lean_object* x_1823; lean_object* x_1824; lean_object* x_1825; 
lean_dec(x_4);
x_1822 = lean_ctor_get(x_1818, 1);
lean_inc(x_1822);
if (lean_is_exclusive(x_1818)) {
 lean_ctor_release(x_1818, 0);
 lean_ctor_release(x_1818, 1);
 x_1823 = x_1818;
} else {
 lean_dec_ref(x_1818);
 x_1823 = lean_box(0);
}
x_1824 = lean_box(0);
if (lean_is_scalar(x_1823)) {
 x_1825 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1825 = x_1823;
}
lean_ctor_set(x_1825, 0, x_1824);
lean_ctor_set(x_1825, 1, x_1822);
x_1574 = x_1825;
x_1575 = x_1819;
goto block_1592;
}
else
{
lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; uint8_t x_1832; 
x_1826 = lean_ctor_get(x_1818, 0);
lean_inc(x_1826);
x_1827 = lean_ctor_get(x_1818, 1);
lean_inc(x_1827);
if (lean_is_exclusive(x_1818)) {
 lean_ctor_release(x_1818, 0);
 lean_ctor_release(x_1818, 1);
 x_1828 = x_1818;
} else {
 lean_dec_ref(x_1818);
 x_1828 = lean_box(0);
}
x_1829 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1830 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_1829, x_6, x_1819);
x_1831 = lean_ctor_get(x_1830, 0);
lean_inc(x_1831);
x_1832 = lean_unbox(x_1831);
lean_dec(x_1831);
if (x_1832 == 0)
{
lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; 
lean_dec(x_1826);
lean_dec(x_4);
x_1833 = lean_ctor_get(x_1830, 1);
lean_inc(x_1833);
lean_dec(x_1830);
x_1834 = lean_box(0);
if (lean_is_scalar(x_1828)) {
 x_1835 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1835 = x_1828;
}
lean_ctor_set(x_1835, 0, x_1834);
lean_ctor_set(x_1835, 1, x_1827);
x_1574 = x_1835;
x_1575 = x_1833;
goto block_1592;
}
else
{
lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; lean_object* x_1843; 
lean_dec(x_1828);
x_1836 = lean_ctor_get(x_1830, 1);
lean_inc(x_1836);
lean_dec(x_1830);
x_1837 = l_Lean_Syntax_formatStxAux___main(x_1549, x_1550, x_1594, x_1826);
x_1838 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1838, 0, x_1837);
x_1839 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_1840 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1840, 0, x_1839);
lean_ctor_set(x_1840, 1, x_1838);
x_1841 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1829, x_1840, x_4, x_1827, x_6, x_1836);
lean_dec(x_4);
x_1842 = lean_ctor_get(x_1841, 0);
lean_inc(x_1842);
x_1843 = lean_ctor_get(x_1841, 1);
lean_inc(x_1843);
lean_dec(x_1841);
x_1574 = x_1842;
x_1575 = x_1843;
goto block_1592;
}
}
}
}
}
}
}
block_1895:
{
lean_object* x_1864; uint8_t x_1865; 
x_1864 = lean_ctor_get(x_1862, 0);
lean_inc(x_1864);
x_1865 = lean_unbox(x_1864);
lean_dec(x_1864);
if (x_1865 == 0)
{
lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; 
x_1866 = lean_ctor_get(x_1862, 1);
lean_inc(x_1866);
if (lean_is_exclusive(x_1862)) {
 lean_ctor_release(x_1862, 0);
 lean_ctor_release(x_1862, 1);
 x_1867 = x_1862;
} else {
 lean_dec_ref(x_1862);
 x_1867 = lean_box(0);
}
x_1868 = lean_box(0);
if (lean_is_scalar(x_1867)) {
 x_1869 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1869 = x_1867;
}
lean_ctor_set(x_1869, 0, x_1868);
lean_ctor_set(x_1869, 1, x_1866);
x_1570 = x_1869;
x_1571 = x_1863;
goto block_1861;
}
else
{
lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; lean_object* x_1878; lean_object* x_1879; lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; 
x_1870 = lean_ctor_get(x_1862, 1);
lean_inc(x_1870);
lean_dec(x_1862);
lean_inc(x_2);
x_1871 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_2);
x_1872 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1872, 0, x_1871);
x_1873 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__17;
x_1874 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1874, 0, x_1873);
lean_ctor_set(x_1874, 1, x_1872);
x_1875 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__20;
x_1876 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1876, 0, x_1874);
lean_ctor_set(x_1876, 1, x_1875);
lean_inc(x_1569);
x_1877 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_1569);
x_1878 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1878, 0, x_1877);
x_1879 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1879, 0, x_1876);
lean_ctor_set(x_1879, 1, x_1878);
x_1880 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_1881 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1881, 0, x_1879);
lean_ctor_set(x_1881, 1, x_1880);
lean_inc(x_1568);
x_1882 = l_Lean_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_1568);
x_1883 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1883, 0, x_1882);
x_1884 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1884, 0, x_1881);
lean_ctor_set(x_1884, 1, x_1883);
x_1885 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__23;
x_1886 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1886, 0, x_1884);
lean_ctor_set(x_1886, 1, x_1885);
x_1887 = lean_ctor_get(x_1501, 1);
lean_inc(x_1887);
x_1888 = l_Lean_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_1887);
x_1889 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1889, 0, x_1888);
x_1890 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1890, 0, x_1886);
lean_ctor_set(x_1890, 1, x_1889);
x_1891 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1892 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1891, x_1890, x_4, x_1870, x_6, x_1863);
x_1893 = lean_ctor_get(x_1892, 0);
lean_inc(x_1893);
x_1894 = lean_ctor_get(x_1892, 1);
lean_inc(x_1894);
lean_dec(x_1892);
x_1570 = x_1893;
x_1571 = x_1894;
goto block_1861;
}
}
}
}
else
{
lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; 
lean_dec(x_1501);
lean_dec(x_1500);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1905 = lean_ctor_get(x_1556, 0);
lean_inc(x_1905);
x_1906 = lean_ctor_get(x_1556, 1);
lean_inc(x_1906);
if (lean_is_exclusive(x_1556)) {
 lean_ctor_release(x_1556, 0);
 lean_ctor_release(x_1556, 1);
 x_1907 = x_1556;
} else {
 lean_dec_ref(x_1556);
 x_1907 = lean_box(0);
}
if (lean_is_scalar(x_1907)) {
 x_1908 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1908 = x_1907;
}
lean_ctor_set(x_1908, 0, x_1905);
lean_ctor_set(x_1908, 1, x_1906);
return x_1908;
}
}
block_1949:
{
lean_object* x_1912; uint8_t x_1913; 
x_1912 = lean_ctor_get(x_1910, 0);
lean_inc(x_1912);
x_1913 = lean_unbox(x_1912);
lean_dec(x_1912);
if (x_1913 == 0)
{
lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; 
lean_dec(x_11);
x_1914 = lean_ctor_get(x_1910, 1);
lean_inc(x_1914);
if (lean_is_exclusive(x_1910)) {
 lean_ctor_release(x_1910, 0);
 lean_ctor_release(x_1910, 1);
 x_1915 = x_1910;
} else {
 lean_dec_ref(x_1910);
 x_1915 = lean_box(0);
}
x_1916 = lean_box(0);
if (lean_is_scalar(x_1915)) {
 x_1917 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1917 = x_1915;
}
lean_ctor_set(x_1917, 0, x_1916);
lean_ctor_set(x_1917, 1, x_1914);
x_1552 = x_1917;
x_1553 = x_1911;
goto block_1909;
}
else
{
lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; 
x_1918 = lean_ctor_get(x_1910, 1);
lean_inc(x_1918);
lean_dec(x_1910);
x_1919 = lean_ctor_get(x_1501, 1);
lean_inc(x_1919);
x_1920 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1920, 0, x_11);
x_1921 = l_Lean_MessageData_ofList___closed__3;
x_1922 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1922, 0, x_1921);
lean_ctor_set(x_1922, 1, x_1920);
x_1923 = lean_unsigned_to_nat(2u);
x_1924 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1924, 0, x_1923);
lean_ctor_set(x_1924, 1, x_1922);
if (lean_obj_tag(x_1919) == 0)
{
lean_object* x_1925; lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; lean_object* x_1930; 
x_1925 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__29;
x_1926 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1926, 0, x_1925);
lean_ctor_set(x_1926, 1, x_1924);
x_1927 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1928 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1927, x_1926, x_4, x_1918, x_6, x_1911);
x_1929 = lean_ctor_get(x_1928, 0);
lean_inc(x_1929);
x_1930 = lean_ctor_get(x_1928, 1);
lean_inc(x_1930);
lean_dec(x_1928);
x_1552 = x_1929;
x_1553 = x_1930;
goto block_1909;
}
else
{
lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; lean_object* x_1946; lean_object* x_1947; lean_object* x_1948; 
x_1931 = lean_ctor_get(x_1919, 0);
lean_inc(x_1931);
lean_dec(x_1919);
x_1932 = l_Nat_repr(x_1931);
x_1933 = l_addParenHeuristic(x_1932);
lean_dec(x_1932);
x_1934 = l_Option_HasRepr___rarg___closed__2;
x_1935 = lean_string_append(x_1934, x_1933);
lean_dec(x_1933);
x_1936 = l_Option_HasRepr___rarg___closed__3;
x_1937 = lean_string_append(x_1935, x_1936);
x_1938 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1938, 0, x_1937);
x_1939 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1939, 0, x_1938);
x_1940 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__26;
x_1941 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1941, 0, x_1940);
lean_ctor_set(x_1941, 1, x_1939);
x_1942 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__27;
x_1943 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1943, 0, x_1941);
lean_ctor_set(x_1943, 1, x_1942);
x_1944 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1944, 0, x_1943);
lean_ctor_set(x_1944, 1, x_1924);
x_1945 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_1946 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1945, x_1944, x_4, x_1918, x_6, x_1911);
x_1947 = lean_ctor_get(x_1946, 0);
lean_inc(x_1947);
x_1948 = lean_ctor_get(x_1946, 1);
lean_inc(x_1948);
lean_dec(x_1946);
x_1552 = x_1947;
x_1553 = x_1948;
goto block_1909;
}
}
}
}
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
x_6 = lean_box(0);
x_7 = 1;
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_7);
x_8 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_1, x_2, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = 1;
x_14 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*4, x_13);
x_15 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_14, x_2, x_3);
return x_15;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("BACKTRACK");
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = lean_apply_4(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 22)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 2)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___closed__1;
x_16 = lean_string_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_17; 
lean_free_object(x_7);
lean_dec(x_8);
x_17 = lean_apply_4(x_2, x_3, x_4, x_5, x_12);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec(x_10);
x_20 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___closed__1;
x_21 = lean_string_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_8);
x_23 = lean_apply_4(x_2, x_3, x_4, x_5, x_18);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_7, 0);
lean_dec(x_25);
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_dec(x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_7);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_7, 0);
lean_dec(x_29);
return x_7;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
lean_dec(x_7);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_7, 0);
lean_dec(x_33);
return x_7;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_dec(x_7);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_mk_antiquot_parenthesizer(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no known parenthesizer for kind '");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_8 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_7, x_6, x_1);
lean_dec(x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = l_Lean_Name_toString___closed__1;
x_10 = l_Lean_Name_toStringWithSep___main(x_9, x_1);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__3;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(22, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_apply_4(x_20, x_2, x_3, x_4, x_5);
return x_21;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
lean_dec(x_2);
x_11 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_4, x_5, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Syntax_getKind(x_14);
lean_inc(x_5);
lean_inc(x_3);
x_17 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind(x_16, x_3, x_15, x_5, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_2 = x_10;
x_4 = x_20;
x_6 = x_19;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_4);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_10);
x_12 = l_Lean_Syntax_getKind(x_10);
x_13 = l_Lean_choiceKind___closed__2;
x_14 = lean_name_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_10);
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_1);
x_17 = lean_box(0);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed), 7, 3);
lean_closure_set(x_20, 0, x_16);
lean_closure_set(x_20, 1, x_17);
lean_closure_set(x_20, 2, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind), 5, 1);
lean_closure_set(x_21, 0, x_12);
x_22 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_20, x_21, x_3, x_11, x_5, x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
lean_dec(x_1);
x_23 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_24 = lean_array_get_size(x_23);
lean_dec(x_23);
lean_inc(x_24);
x_25 = lean_alloc_closure((void*)(l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1___boxed), 6, 2);
lean_closure_set(x_25, 0, x_24);
lean_closure_set(x_25, 1, x_24);
x_26 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_25, x_3, x_11, x_5, x_9);
return x_26;
}
}
}
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = l_Lean_PrettyPrinter_categoryParenthesizerAttribute;
x_9 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_8, x_7, x_1);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_5(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParserOfStack_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(x_10);
lean_dec(x_10);
x_12 = lean_nat_sub(x_11, x_1);
lean_dec(x_11);
x_13 = l_Lean_Syntax_getArg(x_9, x_12);
lean_dec(x_12);
lean_dec(x_9);
x_14 = l_Lean_Syntax_getId(x_13);
lean_dec(x_13);
x_15 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_14, x_2, x_3, x_4, x_5, x_6);
return x_15;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParserOfStack_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_categoryParserOfStack_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
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
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("paren");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Prod_HasRepr___rarg___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Option_HasRepr___rarg___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = l_Array_empty___closed__1;
x_6 = lean_array_push(x_5, x_1);
x_7 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_8 = lean_array_push(x_6, x_7);
x_9 = l_Lean_nullKind___closed__2;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_12 = lean_array_push(x_11, x_10);
x_13 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
x_14 = lean_array_push(x_12, x_13);
x_15 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
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
x_3 = l_Lean_Unhygienic_MonadQuotation___closed__4;
x_4 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Lean_Unhygienic_run___rarg(x_4);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__2), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__3;
x_3 = lean_alloc_ctor(22, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_3, x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_Syntax_getKind(x_10);
x_13 = l_Lean_nullKind;
x_14 = lean_name_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_6);
x_15 = l_Lean_Parser_termParser___closed__2;
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed), 6, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_1);
x_17 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1;
x_18 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_17, x_1, x_16, x_2, x_11, x_4, x_9);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__4;
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_19);
return x_6;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_Syntax_getKind(x_22);
x_25 = l_Lean_nullKind;
x_26 = lean_name_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lean_Parser_termParser___closed__2;
lean_inc(x_1);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed), 6, 2);
lean_closure_set(x_28, 0, x_27);
lean_closure_set(x_28, 1, x_1);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1;
x_30 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_29, x_1, x_28, x_2, x_23, x_4, x_21);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_31 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__4;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_21);
return x_32;
}
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
lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer), 5, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_categoryParenthesizerAttribute;
x_3 = l_Lean_Parser_termParser___closed__2;
x_4 = l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__2;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("seq");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__5() {
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
x_12 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_13 = lean_array_push(x_12, x_11);
x_14 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
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
x_3 = l_Lean_Unhygienic_MonadQuotation___closed__4;
x_4 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Lean_Unhygienic_run___rarg(x_4);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tactic");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__2), 1, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2;
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed), 6, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
x_8 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__3;
x_9 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_8, x_1, x_7, x_2, x_3, x_4, x_5);
return x_9;
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
lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer), 5, 0);
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
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Level");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1___closed__2;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_6 = lean_array_push(x_5, x_1);
x_7 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
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
x_3 = l_Lean_Unhygienic_MonadQuotation___closed__4;
x_4 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Lean_Unhygienic_run___rarg(x_4);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("level");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___lambda__2), 1, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__2;
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore___boxed), 6, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
x_8 = l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__3;
x_9 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_8, x_1, x_7, x_2, x_3, x_4, x_5);
return x_9;
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
lean_object* _init_l___regBuiltin_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_level_parenthesizer), 5, 0);
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_try_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_4(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_4(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_3);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_4(x_1, x_3, x_10, x_5, x_9);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("backtrack");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected node kind '");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', expected '");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_4, x_5, x_6);
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
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
x_14 = l_Lean_Syntax_getKind(x_12);
x_15 = lean_name_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_46; uint8_t x_47; 
lean_dec(x_2);
x_46 = lean_ctor_get(x_9, 4);
lean_inc(x_46);
x_47 = lean_ctor_get_uint8(x_46, sizeof(void*)*1);
lean_dec(x_46);
if (x_47 == 0)
{
uint8_t x_48; lean_object* x_49; 
x_48 = 0;
x_49 = lean_box(x_48);
lean_ctor_set(x_8, 0, x_49);
x_16 = x_8;
x_17 = x_9;
goto block_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_51 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_50, x_5, x_9);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_ctor_set(x_8, 0, x_52);
x_16 = x_8;
x_17 = x_53;
goto block_45;
}
block_45:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_20 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__4;
if (lean_is_scalar(x_10)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_10;
 lean_ctor_set_tag(x_21, 1);
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_10);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = l_Lean_Name_toString___closed__1;
x_24 = l_Lean_Name_toStringWithSep___main(x_23, x_14);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__5;
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__8;
x_30 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Name_toStringWithSep___main(x_23, x_1);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_38 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_37, x_36, x_3, x_22, x_5, x_17);
lean_dec(x_5);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__4;
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__4;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_14);
lean_free_object(x_8);
lean_dec(x_10);
lean_dec(x_1);
x_54 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_2, x_3, x_13, x_5, x_9);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_8, 0);
x_56 = lean_ctor_get(x_8, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_8);
x_57 = l_Lean_Syntax_getKind(x_55);
x_58 = lean_name_eq(x_1, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_87; uint8_t x_88; 
lean_dec(x_2);
x_87 = lean_ctor_get(x_9, 4);
lean_inc(x_87);
x_88 = lean_ctor_get_uint8(x_87, sizeof(void*)*1);
lean_dec(x_87);
if (x_88 == 0)
{
uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_89 = 0;
x_90 = lean_box(x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_56);
x_59 = x_91;
x_60 = x_9;
goto block_86;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_93 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_92, x_5, x_9);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_56);
x_59 = x_96;
x_60 = x_95;
goto block_86;
}
block_86:
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_63 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__4;
if (lean_is_scalar(x_10)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_10;
 lean_ctor_set_tag(x_64, 1);
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_10);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_dec(x_59);
x_66 = l_Lean_Name_toString___closed__1;
x_67 = l_Lean_Name_toStringWithSep___main(x_66, x_57);
x_68 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__5;
x_71 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__8;
x_73 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Name_toStringWithSep___main(x_66, x_1);
x_75 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_79 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_81 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_80, x_79, x_3, x_65, x_5, x_60);
lean_dec(x_5);
lean_dec(x_3);
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
x_84 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__4;
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_83;
 lean_ctor_set_tag(x_85, 1);
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
}
}
else
{
lean_object* x_97; 
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_1);
x_97 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_2, x_3, x_56, x_5, x_9);
return x_97;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_maxPrec;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_4);
x_8 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_2);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(x_2, x_4, x_11, x_6, x_10);
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_12, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_15, 1);
lean_dec(x_20);
x_21 = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___closed__1;
x_22 = l_Nat_min(x_21, x_2);
lean_dec(x_2);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_15, 1, x_23);
x_24 = lean_box(0);
lean_ctor_set(x_13, 0, x_24);
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 2);
x_27 = lean_ctor_get(x_15, 3);
x_28 = lean_ctor_get_uint8(x_15, sizeof(void*)*4);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___closed__1;
x_30 = l_Nat_min(x_29, x_2);
lean_dec(x_2);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_26);
lean_ctor_set(x_32, 3, x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_28);
x_33 = lean_box(0);
lean_ctor_set(x_13, 1, x_32);
lean_ctor_set(x_13, 0, x_33);
return x_12;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_dec(x_12);
x_35 = lean_ctor_get(x_15, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_15, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_15, 3);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_15, sizeof(void*)*4);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 x_39 = x_15;
} else {
 lean_dec_ref(x_15);
 x_39 = lean_box(0);
}
x_40 = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___closed__1;
x_41 = l_Nat_min(x_40, x_2);
lean_dec(x_2);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
if (lean_is_scalar(x_39)) {
 x_43 = lean_alloc_ctor(0, 4, 1);
} else {
 x_43 = x_39;
}
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_36);
lean_ctor_set(x_43, 3, x_37);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_38);
x_44 = lean_box(0);
lean_ctor_set(x_13, 1, x_43);
lean_ctor_set(x_13, 0, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_13);
lean_ctor_set(x_45, 1, x_34);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_46 = lean_ctor_get(x_13, 1);
lean_inc(x_46);
lean_dec(x_13);
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_48 = x_12;
} else {
 lean_dec_ref(x_12);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_46, 3);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_46, sizeof(void*)*4);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_53 = x_46;
} else {
 lean_dec_ref(x_46);
 x_53 = lean_box(0);
}
x_54 = l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___closed__1;
x_55 = l_Nat_min(x_54, x_2);
lean_dec(x_2);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
if (lean_is_scalar(x_53)) {
 x_57 = lean_alloc_ctor(0, 4, 1);
} else {
 x_57 = x_53;
}
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_50);
lean_ctor_set(x_57, 3, x_51);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_52);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
if (lean_is_scalar(x_48)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_48;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_47);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_8);
if (x_61 == 0)
{
return x_8;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_8, 0);
x_63 = lean_ctor_get(x_8, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_8);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_3);
x_7 = lean_apply_4(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_apply_5(x_2, x_10, x_3, x_11, x_5, x_9);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1___rarg), 6, 0);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trailingNode.parenthesizer called outside of maybeParenthesize call");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__7;
x_2 = lean_unsigned_to_nat(356u);
x_3 = lean_unsigned_to_nat(6u);
x_4 = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("someCategory");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(x_1, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_PUnit_Inhabited;
x_13 = l_monadInhabited___rarg(x_2, x_12);
x_14 = lean_alloc_closure((void*)(l_ReaderT_inhabited___rarg___boxed), 2, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__2;
x_16 = lean_panic_fn(x_14, x_15);
x_17 = lean_apply_4(x_16, x_4, x_11, x_6, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__5;
x_23 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_20, x_21, x_22, x_4, x_19, x_6, x_18);
return x_23;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
x_15 = l_Lean_Syntax_getKind(x_13);
x_16 = lean_name_eq(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_47; uint8_t x_48; 
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_ctor_get(x_10, 4);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_47, sizeof(void*)*1);
lean_dec(x_47);
if (x_48 == 0)
{
uint8_t x_49; lean_object* x_50; 
x_49 = 0;
x_50 = lean_box(x_49);
lean_ctor_set(x_9, 0, x_50);
x_17 = x_9;
x_18 = x_10;
goto block_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_52 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_51, x_6, x_10);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_ctor_set(x_9, 0, x_53);
x_17 = x_9;
x_18 = x_54;
goto block_46;
}
block_46:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_21 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__4;
if (lean_is_scalar(x_11)) {
 x_22 = lean_alloc_ctor(1, 2, 0);
} else {
 x_22 = x_11;
 lean_ctor_set_tag(x_22, 1);
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_11);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = l_Lean_Name_toString___closed__1;
x_25 = l_Lean_Name_toStringWithSep___main(x_24, x_15);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__5;
x_29 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__8;
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Name_toStringWithSep___main(x_24, x_1);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_39 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_38, x_37, x_4, x_23, x_6, x_18);
lean_dec(x_6);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__4;
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__4;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_15);
lean_free_object(x_9);
lean_dec(x_11);
lean_dec(x_1);
x_55 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1;
x_56 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___boxed), 7, 2);
lean_closure_set(x_56, 0, x_2);
lean_closure_set(x_56, 1, x_55);
x_57 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1___rarg), 6, 2);
lean_closure_set(x_57, 0, x_3);
lean_closure_set(x_57, 1, x_56);
x_58 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_57, x_4, x_14, x_6, x_10);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_9, 0);
x_60 = lean_ctor_get(x_9, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_9);
x_61 = l_Lean_Syntax_getKind(x_59);
x_62 = lean_name_eq(x_1, x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_91; uint8_t x_92; 
lean_dec(x_3);
lean_dec(x_2);
x_91 = lean_ctor_get(x_10, 4);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_91, sizeof(void*)*1);
lean_dec(x_91);
if (x_92 == 0)
{
uint8_t x_93; lean_object* x_94; lean_object* x_95; 
x_93 = 0;
x_94 = lean_box(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_60);
x_63 = x_95;
x_64 = x_10;
goto block_90;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_97 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_96, x_6, x_10);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_60);
x_63 = x_100;
x_64 = x_99;
goto block_90;
}
block_90:
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_67 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__4;
if (lean_is_scalar(x_11)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_11;
 lean_ctor_set_tag(x_68, 1);
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_11);
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_dec(x_63);
x_70 = l_Lean_Name_toString___closed__1;
x_71 = l_Lean_Name_toStringWithSep___main(x_70, x_61);
x_72 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__5;
x_75 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__8;
x_77 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Name_toStringWithSep___main(x_70, x_1);
x_79 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_83 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_85 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_84, x_83, x_4, x_69, x_6, x_64);
lean_dec(x_6);
lean_dec(x_4);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_88 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__4;
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_87;
 lean_ctor_set_tag(x_89, 1);
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_61);
lean_dec(x_11);
lean_dec(x_1);
x_101 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1;
x_102 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___boxed), 7, 2);
lean_closure_set(x_102, 0, x_2);
lean_closure_set(x_102, 1, x_101);
x_103 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___spec__1___rarg), 6, 2);
lean_closure_set(x_103, 0, x_3);
lean_closure_set(x_103, 1, x_102);
x_104 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_103, x_4, x_60, x_6, x_10);
return x_104;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoWs_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoWs_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_symbolNoWs_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoWs_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_symbolNoWs_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoWs_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_symbolNoWs_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_4);
x_12 = lean_apply_4(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_3 = x_11;
x_5 = x_15;
x_7 = x_14;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer___spec__1___boxed), 7, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_12);
x_14 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_13, x_2, x_10, x_4, x_8);
return x_14;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_many1_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Syntax_getKind(x_9);
x_12 = l_Lean_nullKind;
x_13 = lean_name_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_apply_4(x_1, x_2, x_10, x_4, x_8);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer(x_1, x_2, x_10, x_4, x_8);
return x_15;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_optional_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_List_forM___main___at_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
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
lean_inc(x_6);
lean_inc(x_4);
x_17 = lean_apply_4(x_2, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_3 = x_12;
x_5 = x_20;
x_7 = x_19;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_4);
x_26 = lean_apply_4(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_3 = x_12;
x_5 = x_29;
x_7 = x_28;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_13 = lean_array_get_size(x_12);
lean_dec(x_12);
x_14 = l_List_range(x_13);
x_15 = l_List_reverse___rarg(x_14);
x_16 = lean_alloc_closure((void*)(l_List_forM___main___at_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer___spec__1___boxed), 7, 3);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_15);
x_17 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_16, x_3, x_11, x_5, x_9);
return x_17;
}
}
lean_object* l_List_forM___main___at_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forM___main___at_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepBy1_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer___closed__1;
x_7 = lean_apply_5(x_1, x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_4(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer___rarg), 5, 0);
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_toggleInsideQuot_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_4(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_checkInsideQuot_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_checkOutsideQuot_parenthesizer(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_1 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_4(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_7);
return x_9;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_ite___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_ite___rarg(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_mkAppStx___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1(size_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; size_t x_8; uint8_t x_9; 
x_4 = lean_ptr_addr(x_2);
x_5 = x_1 == 0 ? 0 : x_4 % x_1;
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_array_uget(x_6, x_5);
x_8 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_9 = x_8 == x_4;
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_11 = l_Lean_Expr_isConstOf(x_2, x_10);
if (x_11 == 0)
{
lean_dec(x_6);
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1(x_1, x_12, x_3);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1(x_1, x_13, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_inc(x_2);
x_22 = lean_array_uset(x_21, x_5, x_2);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_expr_update_app(x_2, x_15, x_19);
lean_inc(x_24);
x_25 = lean_array_uset(x_23, x_5, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_17, 1, x_26);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_inc(x_2);
x_30 = lean_array_uset(x_29, x_5, x_2);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_expr_update_app(x_2, x_15, x_27);
lean_inc(x_32);
x_33 = lean_array_uset(x_31, x_5, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
case 6:
{
lean_object* x_36; lean_object* x_37; uint64_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 2);
lean_inc(x_37);
x_38 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_39 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1(x_1, x_36, x_3);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1(x_1, x_37, x_41);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_inc(x_2);
x_47 = lean_array_uset(x_46, x_5, x_2);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = (uint8_t)((x_38 << 24) >> 61);
x_50 = lean_expr_update_lambda(x_2, x_49, x_40, x_44);
lean_inc(x_50);
x_51 = lean_array_uset(x_48, x_5, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_42, 1, x_52);
lean_ctor_set(x_42, 0, x_50);
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_inc(x_2);
x_56 = lean_array_uset(x_55, x_5, x_2);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = (uint8_t)((x_38 << 24) >> 61);
x_59 = lean_expr_update_lambda(x_2, x_58, x_40, x_53);
lean_inc(x_59);
x_60 = lean_array_uset(x_57, x_5, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
case 7:
{
lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_63 = lean_ctor_get(x_2, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_2, 2);
lean_inc(x_64);
x_65 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_66 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1(x_1, x_63, x_3);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1(x_1, x_64, x_68);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_inc(x_2);
x_74 = lean_array_uset(x_73, x_5, x_2);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = (uint8_t)((x_65 << 24) >> 61);
x_77 = lean_expr_update_forall(x_2, x_76, x_67, x_71);
lean_inc(x_77);
x_78 = lean_array_uset(x_75, x_5, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_69, 1, x_79);
lean_ctor_set(x_69, 0, x_77);
return x_69;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_80 = lean_ctor_get(x_69, 0);
x_81 = lean_ctor_get(x_69, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_69);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_inc(x_2);
x_83 = lean_array_uset(x_82, x_5, x_2);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = (uint8_t)((x_65 << 24) >> 61);
x_86 = lean_expr_update_forall(x_2, x_85, x_67, x_80);
lean_inc(x_86);
x_87 = lean_array_uset(x_84, x_5, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
case 8:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_90 = lean_ctor_get(x_2, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_2, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_2, 3);
lean_inc(x_92);
x_93 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1(x_1, x_90, x_3);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1(x_1, x_91, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1(x_1, x_92, x_98);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ctor_get(x_99, 1);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_inc(x_2);
x_104 = lean_array_uset(x_103, x_5, x_2);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_expr_update_let(x_2, x_94, x_97, x_101);
lean_inc(x_106);
x_107 = lean_array_uset(x_105, x_5, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_99, 1, x_108);
lean_ctor_set(x_99, 0, x_106);
return x_99;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_109 = lean_ctor_get(x_99, 0);
x_110 = lean_ctor_get(x_99, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_99);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_inc(x_2);
x_112 = lean_array_uset(x_111, x_5, x_2);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
x_114 = lean_expr_update_let(x_2, x_94, x_97, x_109);
lean_inc(x_114);
x_115 = lean_array_uset(x_113, x_5, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_112);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
case 10:
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_2, 1);
lean_inc(x_118);
x_119 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1(x_1, x_118, x_3);
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_121 = lean_ctor_get(x_119, 0);
x_122 = lean_ctor_get(x_119, 1);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_inc(x_2);
x_124 = lean_array_uset(x_123, x_5, x_2);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec(x_122);
x_126 = lean_expr_update_mdata(x_2, x_121);
lean_inc(x_126);
x_127 = lean_array_uset(x_125, x_5, x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_124);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_119, 1, x_128);
lean_ctor_set(x_119, 0, x_126);
return x_119;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_129 = lean_ctor_get(x_119, 0);
x_130 = lean_ctor_get(x_119, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_119);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_inc(x_2);
x_132 = lean_array_uset(x_131, x_5, x_2);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_expr_update_mdata(x_2, x_129);
lean_inc(x_134);
x_135 = lean_array_uset(x_133, x_5, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_132);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
case 11:
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_138 = lean_ctor_get(x_2, 2);
lean_inc(x_138);
x_139 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1(x_1, x_138, x_3);
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_141 = lean_ctor_get(x_139, 0);
x_142 = lean_ctor_get(x_139, 1);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_inc(x_2);
x_144 = lean_array_uset(x_143, x_5, x_2);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = lean_expr_update_proj(x_2, x_141);
lean_inc(x_146);
x_147 = lean_array_uset(x_145, x_5, x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_144);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_139, 1, x_148);
lean_ctor_set(x_139, 0, x_146);
return x_139;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_149 = lean_ctor_get(x_139, 0);
x_150 = lean_ctor_get(x_139, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_139);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_inc(x_2);
x_152 = lean_array_uset(x_151, x_5, x_2);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
x_154 = lean_expr_update_proj(x_2, x_149);
lean_inc(x_154);
x_155 = lean_array_uset(x_153, x_5, x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_152);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
case 12:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_2);
x_158 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2;
x_159 = l_unreachable_x21___rarg(x_158);
x_160 = lean_apply_1(x_159, x_3);
return x_160;
}
default: 
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_2);
lean_ctor_set(x_161, 1, x_3);
return x_161;
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_162 = lean_array_uset(x_6, x_5, x_2);
x_163 = lean_ctor_get(x_3, 1);
lean_inc(x_163);
lean_dec(x_3);
x_164 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__2;
x_165 = lean_array_uset(x_163, x_5, x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_162);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_6);
lean_dec(x_2);
x_168 = lean_ctor_get(x_3, 1);
lean_inc(x_168);
x_169 = lean_array_uget(x_168, x_5);
lean_dec(x_168);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_3);
return x_170;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = 8192;
x_3 = l_Lean_Expr_ReplaceImpl_initCache;
x_4 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1(x_2, x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_1);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_1, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_29 = lean_name_mk_string(x_27, x_28);
x_30 = l_Lean_Expr_isConstOf(x_24, x_29);
lean_dec(x_29);
lean_dec(x_24);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_31;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_8);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_17, x_8, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_19;
x_7 = x_36;
x_9 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_20);
if (x_46 == 0)
{
return x_20;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_20, 0);
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_20);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_mkAppStx___closed__3;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_Expr_isConstOf(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
lean_object* _init_l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_2, x_4);
x_15 = lean_array_fget(x_3, x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
lean_inc(x_6);
x_18 = l_Lean_Meta_inferType(x_14, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_6);
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_6, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
x_26 = l_Lean_Expr_isConstOf(x_23, x_25);
lean_dec(x_23);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_mkApp(x_5, x_15);
x_4 = x_17;
x_5 = x_27;
x_7 = x_24;
goto _start;
}
else
{
lean_object* x_29; 
lean_inc(x_6);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_15, x_6, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_mkApp(x_5, x_30);
x_4 = x_17;
x_5 = x_32;
x_7 = x_31;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
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
uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_1);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_1, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_29 = lean_name_mk_string(x_27, x_28);
x_30 = l_Lean_Expr_isConstOf(x_24, x_29);
lean_dec(x_29);
lean_dec(x_24);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_31;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_8);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_17, x_8, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_19;
x_7 = x_36;
x_9 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_20);
if (x_46 == 0)
{
return x_20;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_20, 0);
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_20);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_2, x_4);
x_15 = lean_array_fget(x_3, x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
lean_inc(x_6);
x_18 = l_Lean_Meta_inferType(x_14, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_6);
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_6, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
x_26 = l_Lean_Expr_isConstOf(x_23, x_25);
lean_dec(x_23);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_mkApp(x_5, x_15);
x_4 = x_17;
x_5 = x_27;
x_7 = x_24;
goto _start;
}
else
{
lean_object* x_29; 
lean_inc(x_6);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_15, x_6, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_mkApp(x_5, x_30);
x_4 = x_17;
x_5 = x_32;
x_7 = x_31;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
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
uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_1);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_1, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_29 = lean_name_mk_string(x_27, x_28);
x_30 = l_Lean_Expr_isConstOf(x_24, x_29);
lean_dec(x_29);
lean_dec(x_24);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_31;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_8);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_17, x_8, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_19;
x_7 = x_36;
x_9 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_20);
if (x_46 == 0)
{
return x_20;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_20, 0);
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_20);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_2, x_4);
x_15 = lean_array_fget(x_3, x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
lean_inc(x_6);
x_18 = l_Lean_Meta_inferType(x_14, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_6);
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_6, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
x_26 = l_Lean_Expr_isConstOf(x_23, x_25);
lean_dec(x_23);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_mkApp(x_5, x_15);
x_4 = x_17;
x_5 = x_27;
x_7 = x_24;
goto _start;
}
else
{
lean_object* x_29; 
lean_inc(x_6);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_15, x_6, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_mkApp(x_5, x_30);
x_4 = x_17;
x_5 = x_32;
x_7 = x_31;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
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
uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_1);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_1, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_29 = lean_name_mk_string(x_27, x_28);
x_30 = l_Lean_Expr_isConstOf(x_24, x_29);
lean_dec(x_29);
lean_dec(x_24);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_31;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_8);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_17, x_8, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_19;
x_7 = x_36;
x_9 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_20);
if (x_46 == 0)
{
return x_20;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_20, 0);
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_20);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_2, x_4);
x_15 = lean_array_fget(x_3, x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
lean_inc(x_6);
x_18 = l_Lean_Meta_inferType(x_14, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_6);
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_6, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
x_26 = l_Lean_Expr_isConstOf(x_23, x_25);
lean_dec(x_23);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_mkApp(x_5, x_15);
x_4 = x_17;
x_5 = x_27;
x_7 = x_24;
goto _start;
}
else
{
lean_object* x_29; 
lean_inc(x_6);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_15, x_6, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_mkApp(x_5, x_30);
x_4 = x_17;
x_5 = x_32;
x_7 = x_31;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
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
uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_1);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_1, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_29 = lean_name_mk_string(x_27, x_28);
x_30 = l_Lean_Expr_isConstOf(x_24, x_29);
lean_dec(x_29);
lean_dec(x_24);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_31;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_8);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_17, x_8, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_19;
x_7 = x_36;
x_9 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_20);
if (x_46 == 0)
{
return x_20;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_20, 0);
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_20);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_2, x_4);
x_15 = lean_array_fget(x_3, x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
lean_inc(x_6);
x_18 = l_Lean_Meta_inferType(x_14, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_6);
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_6, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
x_26 = l_Lean_Expr_isConstOf(x_23, x_25);
lean_dec(x_23);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_mkApp(x_5, x_15);
x_4 = x_17;
x_5 = x_27;
x_7 = x_24;
goto _start;
}
else
{
lean_object* x_29; 
lean_inc(x_6);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_15, x_6, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_mkApp(x_5, x_30);
x_4 = x_17;
x_5 = x_32;
x_7 = x_31;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
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
uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_1);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_1, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_29 = lean_name_mk_string(x_27, x_28);
x_30 = l_Lean_Expr_isConstOf(x_24, x_29);
lean_dec(x_29);
lean_dec(x_24);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_31;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_8);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_17, x_8, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_19;
x_7 = x_36;
x_9 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_20);
if (x_46 == 0)
{
return x_20;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_20, 0);
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_20);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_2, x_4);
x_15 = lean_array_fget(x_3, x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
lean_inc(x_6);
x_18 = l_Lean_Meta_inferType(x_14, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_6);
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_6, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
x_26 = l_Lean_Expr_isConstOf(x_23, x_25);
lean_dec(x_23);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_mkApp(x_5, x_15);
x_4 = x_17;
x_5 = x_27;
x_7 = x_24;
goto _start;
}
else
{
lean_object* x_29; 
lean_inc(x_6);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_15, x_6, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_mkApp(x_5, x_30);
x_4 = x_17;
x_5 = x_32;
x_7 = x_31;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
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
uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_1);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_1, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_29 = lean_name_mk_string(x_27, x_28);
x_30 = l_Lean_Expr_isConstOf(x_24, x_29);
lean_dec(x_29);
lean_dec(x_24);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_31;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_8);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_17, x_8, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_19;
x_7 = x_36;
x_9 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_20);
if (x_46 == 0)
{
return x_20;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_20, 0);
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_20);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_2, x_4);
x_15 = lean_array_fget(x_3, x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
lean_inc(x_6);
x_18 = l_Lean_Meta_inferType(x_14, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_6);
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_6, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
x_26 = l_Lean_Expr_isConstOf(x_23, x_25);
lean_dec(x_23);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_mkApp(x_5, x_15);
x_4 = x_17;
x_5 = x_27;
x_7 = x_24;
goto _start;
}
else
{
lean_object* x_29; 
lean_inc(x_6);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_15, x_6, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_mkApp(x_5, x_30);
x_4 = x_17;
x_5 = x_32;
x_7 = x_31;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
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
uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_1);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_1, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_29 = lean_name_mk_string(x_27, x_28);
x_30 = l_Lean_Expr_isConstOf(x_24, x_29);
lean_dec(x_29);
lean_dec(x_24);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_31;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_8);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_17, x_8, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_19;
x_7 = x_36;
x_9 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_20);
if (x_46 == 0)
{
return x_20;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_20, 0);
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_20);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_2, x_4);
x_15 = lean_array_fget(x_3, x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
lean_inc(x_6);
x_18 = l_Lean_Meta_inferType(x_14, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_6);
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_6, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
x_26 = l_Lean_Expr_isConstOf(x_23, x_25);
lean_dec(x_23);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_mkApp(x_5, x_15);
x_4 = x_17;
x_5 = x_27;
x_7 = x_24;
goto _start;
}
else
{
lean_object* x_29; 
lean_inc(x_6);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_15, x_6, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_mkApp(x_5, x_30);
x_4 = x_17;
x_5 = x_32;
x_7 = x_31;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
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
uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_1);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_1, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_29 = lean_name_mk_string(x_27, x_28);
x_30 = l_Lean_Expr_isConstOf(x_24, x_29);
lean_dec(x_29);
lean_dec(x_24);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_31;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_8);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_17, x_8, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_19;
x_7 = x_36;
x_9 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_20);
if (x_46 == 0)
{
return x_20;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_20, 0);
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_20);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_2, x_4);
x_15 = lean_array_fget(x_3, x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
lean_inc(x_6);
x_18 = l_Lean_Meta_inferType(x_14, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_6);
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_6, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
x_26 = l_Lean_Expr_isConstOf(x_23, x_25);
lean_dec(x_23);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_mkApp(x_5, x_15);
x_4 = x_17;
x_5 = x_27;
x_7 = x_24;
goto _start;
}
else
{
lean_object* x_29; 
lean_inc(x_6);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_15, x_6, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_mkApp(x_5, x_30);
x_4 = x_17;
x_5 = x_32;
x_7 = x_31;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
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
uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_1);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_1, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_29 = lean_name_mk_string(x_27, x_28);
x_30 = l_Lean_Expr_isConstOf(x_24, x_29);
lean_dec(x_29);
lean_dec(x_24);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_31;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_8);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_17, x_8, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_19;
x_7 = x_36;
x_9 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_20);
if (x_46 == 0)
{
return x_20;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_20, 0);
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_20);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_2, x_4);
x_15 = lean_array_fget(x_3, x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
lean_inc(x_6);
x_18 = l_Lean_Meta_inferType(x_14, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_6);
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_6, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
x_26 = l_Lean_Expr_isConstOf(x_23, x_25);
lean_dec(x_23);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_mkApp(x_5, x_15);
x_4 = x_17;
x_5 = x_27;
x_7 = x_24;
goto _start;
}
else
{
lean_object* x_29; 
lean_inc(x_6);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_15, x_6, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_mkApp(x_5, x_30);
x_4 = x_17;
x_5 = x_32;
x_7 = x_31;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
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
uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_4, x_6);
x_17 = lean_array_fget(x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
lean_inc(x_8);
x_20 = l_Lean_Meta_inferType(x_16, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_1);
x_23 = l_Lean_Meta_forallTelescope___rarg(x_21, x_1, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_29 = lean_name_mk_string(x_27, x_28);
x_30 = l_Lean_Expr_isConstOf(x_24, x_29);
lean_dec(x_29);
lean_dec(x_24);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_mkApp(x_7, x_17);
x_6 = x_19;
x_7 = x_31;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_33; 
lean_inc(x_8);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_17, x_8, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkApp(x_7, x_34);
x_6 = x_19;
x_7 = x_36;
x_9 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_20);
if (x_46 == 0)
{
return x_20;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_20, 0);
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_20);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = lean_array_fget(x_4, x_13);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_14, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___lambda__1___boxed), 6, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_inc(x_8);
x_19 = l_Lean_Meta_forallTelescope___rarg(x_16, x_18, x_8, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkThunk___closed__1;
x_23 = 0;
x_24 = l_Lean_mkForall(x_22, x_23, x_20, x_7);
x_5 = x_13;
x_6 = lean_box(0);
x_7 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_2, x_4);
x_15 = lean_array_fget(x_3, x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
lean_inc(x_6);
x_18 = l_Lean_Meta_inferType(x_14, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_6);
x_22 = l_Lean_Meta_forallTelescope___rarg(x_19, x_21, x_6, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
x_26 = l_Lean_Expr_isConstOf(x_23, x_25);
lean_dec(x_23);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_mkApp(x_5, x_15);
x_4 = x_17;
x_5 = x_27;
x_7 = x_24;
goto _start;
}
else
{
lean_object* x_29; 
lean_inc(x_6);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_15, x_6, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_mkApp(x_5, x_30);
x_4 = x_17;
x_5 = x_32;
x_7 = x_31;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
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
uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__1(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_10 = lean_name_mk_string(x_8, x_9);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6);
return x_14;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3(x_3, x_3, x_1, x_7, x_2, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__4(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_10 = lean_name_mk_string(x_8, x_9);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__5(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6);
return x_14;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__6(x_3, x_3, x_1, x_7, x_2, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__7(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_10 = lean_name_mk_string(x_8, x_9);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__8(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6);
return x_14;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__9(x_3, x_3, x_1, x_7, x_2, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__10(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_10 = lean_name_mk_string(x_8, x_9);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__11(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6);
return x_14;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__12(x_3, x_3, x_1, x_7, x_2, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__13(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_10 = lean_name_mk_string(x_8, x_9);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__14(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6);
return x_14;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__15(x_3, x_3, x_1, x_7, x_2, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Meta_mkLambda(x_1, x_6, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__16(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_10 = lean_name_mk_string(x_8, x_9);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__17(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6);
return x_14;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__18(x_3, x_3, x_1, x_7, x_2, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__19(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_10 = lean_name_mk_string(x_8, x_9);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__20(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6);
return x_14;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__21(x_3, x_3, x_1, x_7, x_2, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__22(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_10 = lean_name_mk_string(x_8, x_9);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__23(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6);
return x_14;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__24(x_3, x_3, x_1, x_7, x_2, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__25(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_10 = lean_name_mk_string(x_8, x_9);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__26(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6);
return x_14;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__27(x_3, x_3, x_1, x_7, x_2, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__28(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_10 = lean_name_mk_string(x_8, x_9);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__29(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6);
return x_14;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__30(x_3, x_3, x_1, x_7, x_2, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__31(x_1, x_2, x_5, x_5, x_3, x_9, x_4, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_10 = lean_name_mk_string(x_8, x_9);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_10, x_11);
x_13 = lean_array_get_size(x_3);
lean_inc(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__32(x_2, x_3, x_12, x_3, x_13, lean_box(0), x_12, x_5, x_6);
return x_14;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__33(x_3, x_3, x_1, x_7, x_2, x_5, x_6);
return x_8;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("call of unknown parser at '");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("don't know how to generate parenthesizer for non-definition '");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_mkAppStx___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__2___boxed), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_Parser_mkParserOfConstantUnsafe___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("don't know how to generate parenthesizer for non-parser combinator '");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_mkAppStx___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__5___boxed), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_mkAppStx___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__8___boxed), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_mkAppStx___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__11___boxed), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_mkAppStx___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__14___boxed), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__16), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_mkAppStx___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__18___boxed), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_mkAppStx___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__21___boxed), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_mkAppStx___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__24___boxed), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_mkAppStx___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__27___boxed), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_mkAppStx___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__30___boxed), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_mkAppStx___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__33___boxed), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_20);
x_22 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_21);
x_23 = lean_mk_array(x_21, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_21, x_24);
lean_dec(x_21);
lean_inc(x_5);
x_26 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_23, x_25);
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
x_28 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_29 = l_Lean_CombinatorCompilerAttribute_getDeclFor(x_28, x_27, x_19);
lean_dec(x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
x_31 = l_Lean_Name_append___main(x_19, x_30);
lean_inc(x_19);
x_32 = l_Lean_Meta_getConstInfo(x_19, x_2, x_6);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_ConstantInfo_type(x_33);
x_36 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_35);
x_37 = l_Lean_Meta_forallTelescope___rarg(x_35, x_36, x_2, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_109; uint8_t x_110; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_109 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8;
x_110 = l_Lean_Expr_isConstOf(x_38, x_109);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_112 = l_Lean_Expr_isConstOf(x_38, x_111);
lean_dec(x_38);
if (x_112 == 0)
{
lean_object* x_113; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_19);
lean_inc(x_2);
lean_inc(x_5);
x_113 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_39);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_117 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__11;
x_120 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_122 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_box(0);
x_124 = l_Lean_Meta_throwOther___rarg(x_122, x_123, x_2, x_115);
lean_dec(x_2);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_5);
x_125 = lean_ctor_get(x_113, 1);
lean_inc(x_125);
lean_dec(x_113);
x_126 = lean_ctor_get(x_114, 0);
lean_inc(x_126);
lean_dec(x_114);
x_1 = x_126;
x_3 = x_125;
goto _start;
}
}
else
{
uint8_t x_128; 
lean_dec(x_5);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_113);
if (x_128 == 0)
{
return x_113;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_113, 0);
x_130 = lean_ctor_get(x_113, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_113);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
lean_object* x_132; 
x_132 = lean_box(0);
x_40 = x_132;
goto block_108;
}
}
else
{
lean_object* x_133; 
lean_dec(x_38);
x_133 = lean_box(0);
x_40 = x_133;
goto block_108;
}
block_108:
{
lean_object* x_41; 
lean_dec(x_40);
x_41 = l_Lean_ConstantInfo_value_x3f(x_33);
lean_dec(x_33);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_19);
x_42 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_46 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_48 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_box(0);
x_50 = l_Lean_Meta_throwOther___rarg(x_48, x_49, x_2, x_39);
lean_dec(x_2);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_5);
x_51 = lean_ctor_get(x_41, 0);
lean_inc(x_51);
lean_dec(x_41);
x_52 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_51);
lean_inc(x_2);
x_53 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_52, x_2, x_39);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_74; lean_object* x_75; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_74 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__7;
lean_inc(x_2);
x_75 = l_Lean_Meta_forallTelescope___rarg(x_35, x_74, x_2, x_55);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_box(0);
lean_inc(x_31);
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_31);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_79, 2, x_76);
x_80 = lean_box(0);
x_81 = 0;
x_82 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_54);
lean_ctor_set(x_82, 2, x_80);
lean_ctor_set_uint8(x_82, sizeof(void*)*3, x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_ctor_get(x_77, 0);
lean_inc(x_84);
x_85 = l_Lean_Options_empty;
x_86 = l_Lean_Environment_addAndCompile(x_84, x_85, x_83);
lean_dec(x_83);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_19);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_Lean_KernelException_toMessageData(x_87, x_85);
x_89 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_88);
x_90 = l_Lean_Format_pretty(x_89, x_85);
x_91 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_box(0);
x_94 = l_Lean_Meta_throwOther___rarg(x_92, x_93, x_2, x_77);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
return x_94;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_94);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
else
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_86, 0);
lean_inc(x_99);
lean_dec(x_86);
x_56 = x_99;
x_57 = x_77;
goto block_73;
}
}
else
{
uint8_t x_100; 
lean_dec(x_54);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_75);
if (x_100 == 0)
{
return x_75;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_75, 0);
x_102 = lean_ctor_get(x_75, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_75);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
block_73:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_inc(x_31);
x_58 = l_Lean_CombinatorCompilerAttribute_setDeclFor(x_28, x_56, x_19, x_31);
x_59 = l_Lean_Meta_setEnv(x_58, x_2, x_57);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_box(0);
x_62 = l_Lean_mkConst(x_31, x_61);
lean_inc(x_2);
lean_inc(x_62);
x_63 = l_Lean_Meta_inferType(x_62, x_2, x_60);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_mkAppStx___closed__2;
x_67 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__1___boxed), 8, 4);
lean_closure_set(x_67, 0, x_36);
lean_closure_set(x_67, 1, x_66);
lean_closure_set(x_67, 2, x_26);
lean_closure_set(x_67, 3, x_62);
x_68 = l_Lean_Meta_forallTelescope___rarg(x_64, x_67, x_2, x_65);
return x_68;
}
else
{
uint8_t x_69; 
lean_dec(x_62);
lean_dec(x_26);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_63);
if (x_69 == 0)
{
return x_63;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_63, 0);
x_71 = lean_ctor_get(x_63, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_63);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_2);
x_104 = !lean_is_exclusive(x_53);
if (x_104 == 0)
{
return x_53;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_53, 0);
x_106 = lean_ctor_get(x_53, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_53);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_2);
x_134 = !lean_is_exclusive(x_37);
if (x_134 == 0)
{
return x_37;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_37, 0);
x_136 = lean_ctor_get(x_37, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_37);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_2);
x_138 = !lean_is_exclusive(x_32);
if (x_138 == 0)
{
return x_32;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_32, 0);
x_140 = lean_ctor_get(x_32, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_32);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_19);
lean_dec(x_5);
x_142 = lean_ctor_get(x_29, 0);
lean_inc(x_142);
lean_dec(x_29);
x_143 = lean_box(0);
x_144 = l_Lean_mkConst(x_142, x_143);
lean_inc(x_2);
lean_inc(x_144);
x_145 = l_Lean_Meta_inferType(x_144, x_2, x_6);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__3___boxed), 6, 2);
lean_closure_set(x_148, 0, x_26);
lean_closure_set(x_148, 1, x_144);
x_149 = l_Lean_Meta_forallTelescope___rarg(x_146, x_148, x_2, x_147);
return x_149;
}
else
{
uint8_t x_150; 
lean_dec(x_144);
lean_dec(x_26);
lean_dec(x_2);
x_150 = !lean_is_exclusive(x_145);
if (x_150 == 0)
{
return x_145;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_145, 0);
x_152 = lean_ctor_get(x_145, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_145);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
}
else
{
lean_object* x_154; 
lean_dec(x_7);
x_154 = lean_box(0);
x_8 = x_154;
goto block_18;
}
block_18:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
x_9 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = l_Lean_Meta_throwOther___rarg(x_15, x_16, x_2, x_6);
lean_dec(x_2);
return x_17;
}
}
case 1:
{
uint8_t x_155; 
lean_dec(x_2);
x_155 = !lean_is_exclusive(x_4);
if (x_155 == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_4, 0);
lean_dec(x_156);
return x_4;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_4, 1);
lean_inc(x_157);
lean_dec(x_4);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_5);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
case 2:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_4, 1);
lean_inc(x_159);
lean_dec(x_4);
x_160 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_160) == 4)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_172 = lean_ctor_get(x_160, 0);
lean_inc(x_172);
lean_dec(x_160);
x_173 = lean_unsigned_to_nat(0u);
x_174 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_173);
x_175 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_174);
x_176 = lean_mk_array(x_174, x_175);
x_177 = lean_unsigned_to_nat(1u);
x_178 = lean_nat_sub(x_174, x_177);
lean_dec(x_174);
lean_inc(x_5);
x_179 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_176, x_178);
x_180 = lean_ctor_get(x_159, 0);
lean_inc(x_180);
x_181 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_182 = l_Lean_CombinatorCompilerAttribute_getDeclFor(x_181, x_180, x_172);
lean_dec(x_180);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
x_184 = l_Lean_Name_append___main(x_172, x_183);
lean_inc(x_172);
x_185 = l_Lean_Meta_getConstInfo(x_172, x_2, x_159);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = l_Lean_ConstantInfo_type(x_186);
x_189 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_188);
x_190 = l_Lean_Meta_forallTelescope___rarg(x_188, x_189, x_2, x_187);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_262; uint8_t x_263; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_262 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8;
x_263 = l_Lean_Expr_isConstOf(x_191, x_262);
if (x_263 == 0)
{
lean_object* x_264; uint8_t x_265; 
x_264 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_265 = l_Lean_Expr_isConstOf(x_191, x_264);
lean_dec(x_191);
if (x_265 == 0)
{
lean_object* x_266; 
lean_dec(x_188);
lean_dec(x_186);
lean_dec(x_184);
lean_dec(x_179);
lean_dec(x_172);
lean_inc(x_2);
lean_inc(x_5);
x_266 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_192);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_270 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_270, 0, x_269);
x_271 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_271, 0, x_270);
x_272 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__11;
x_273 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_271);
x_274 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_275 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
x_276 = lean_box(0);
x_277 = l_Lean_Meta_throwOther___rarg(x_275, x_276, x_2, x_268);
lean_dec(x_2);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; 
lean_dec(x_5);
x_278 = lean_ctor_get(x_266, 1);
lean_inc(x_278);
lean_dec(x_266);
x_279 = lean_ctor_get(x_267, 0);
lean_inc(x_279);
lean_dec(x_267);
x_1 = x_279;
x_3 = x_278;
goto _start;
}
}
else
{
uint8_t x_281; 
lean_dec(x_5);
lean_dec(x_2);
x_281 = !lean_is_exclusive(x_266);
if (x_281 == 0)
{
return x_266;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_266, 0);
x_283 = lean_ctor_get(x_266, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_266);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
}
else
{
lean_object* x_285; 
x_285 = lean_box(0);
x_193 = x_285;
goto block_261;
}
}
else
{
lean_object* x_286; 
lean_dec(x_191);
x_286 = lean_box(0);
x_193 = x_286;
goto block_261;
}
block_261:
{
lean_object* x_194; 
lean_dec(x_193);
x_194 = l_Lean_ConstantInfo_value_x3f(x_186);
lean_dec(x_186);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_188);
lean_dec(x_184);
lean_dec(x_179);
lean_dec(x_172);
x_195 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_196 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_196, 0, x_195);
x_197 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_198 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_199 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_200 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_201 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_box(0);
x_203 = l_Lean_Meta_throwOther___rarg(x_201, x_202, x_2, x_192);
lean_dec(x_2);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_5);
x_204 = lean_ctor_get(x_194, 0);
lean_inc(x_204);
lean_dec(x_194);
x_205 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_204);
lean_inc(x_2);
x_206 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_205, x_2, x_192);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_227; lean_object* x_228; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_227 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__12;
lean_inc(x_2);
x_228 = l_Lean_Meta_forallTelescope___rarg(x_188, x_227, x_2, x_208);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = lean_box(0);
lean_inc(x_184);
x_232 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_232, 0, x_184);
lean_ctor_set(x_232, 1, x_231);
lean_ctor_set(x_232, 2, x_229);
x_233 = lean_box(0);
x_234 = 0;
x_235 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_207);
lean_ctor_set(x_235, 2, x_233);
lean_ctor_set_uint8(x_235, sizeof(void*)*3, x_234);
x_236 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_236, 0, x_235);
x_237 = lean_ctor_get(x_230, 0);
lean_inc(x_237);
x_238 = l_Lean_Options_empty;
x_239 = l_Lean_Environment_addAndCompile(x_237, x_238, x_236);
lean_dec(x_236);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
lean_dec(x_184);
lean_dec(x_179);
lean_dec(x_172);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
lean_dec(x_239);
x_241 = l_Lean_KernelException_toMessageData(x_240, x_238);
x_242 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_241);
x_243 = l_Lean_Format_pretty(x_242, x_238);
x_244 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_244, 0, x_243);
x_245 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_245, 0, x_244);
x_246 = lean_box(0);
x_247 = l_Lean_Meta_throwOther___rarg(x_245, x_246, x_2, x_230);
lean_dec(x_2);
x_248 = !lean_is_exclusive(x_247);
if (x_248 == 0)
{
return x_247;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_247, 0);
x_250 = lean_ctor_get(x_247, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_247);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
else
{
lean_object* x_252; 
x_252 = lean_ctor_get(x_239, 0);
lean_inc(x_252);
lean_dec(x_239);
x_209 = x_252;
x_210 = x_230;
goto block_226;
}
}
else
{
uint8_t x_253; 
lean_dec(x_207);
lean_dec(x_184);
lean_dec(x_179);
lean_dec(x_172);
lean_dec(x_2);
x_253 = !lean_is_exclusive(x_228);
if (x_253 == 0)
{
return x_228;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_228, 0);
x_255 = lean_ctor_get(x_228, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_228);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
block_226:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_inc(x_184);
x_211 = l_Lean_CombinatorCompilerAttribute_setDeclFor(x_181, x_209, x_172, x_184);
x_212 = l_Lean_Meta_setEnv(x_211, x_2, x_210);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
x_214 = lean_box(0);
x_215 = l_Lean_mkConst(x_184, x_214);
lean_inc(x_2);
lean_inc(x_215);
x_216 = l_Lean_Meta_inferType(x_215, x_2, x_213);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = l_Lean_mkAppStx___closed__2;
x_220 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__4___boxed), 8, 4);
lean_closure_set(x_220, 0, x_189);
lean_closure_set(x_220, 1, x_219);
lean_closure_set(x_220, 2, x_179);
lean_closure_set(x_220, 3, x_215);
x_221 = l_Lean_Meta_forallTelescope___rarg(x_217, x_220, x_2, x_218);
return x_221;
}
else
{
uint8_t x_222; 
lean_dec(x_215);
lean_dec(x_179);
lean_dec(x_2);
x_222 = !lean_is_exclusive(x_216);
if (x_222 == 0)
{
return x_216;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_216, 0);
x_224 = lean_ctor_get(x_216, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_216);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
}
else
{
uint8_t x_257; 
lean_dec(x_188);
lean_dec(x_184);
lean_dec(x_179);
lean_dec(x_172);
lean_dec(x_2);
x_257 = !lean_is_exclusive(x_206);
if (x_257 == 0)
{
return x_206;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_206, 0);
x_259 = lean_ctor_get(x_206, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_206);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
}
}
else
{
uint8_t x_287; 
lean_dec(x_188);
lean_dec(x_186);
lean_dec(x_184);
lean_dec(x_179);
lean_dec(x_172);
lean_dec(x_5);
lean_dec(x_2);
x_287 = !lean_is_exclusive(x_190);
if (x_287 == 0)
{
return x_190;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_190, 0);
x_289 = lean_ctor_get(x_190, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_190);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
return x_290;
}
}
}
else
{
uint8_t x_291; 
lean_dec(x_184);
lean_dec(x_179);
lean_dec(x_172);
lean_dec(x_5);
lean_dec(x_2);
x_291 = !lean_is_exclusive(x_185);
if (x_291 == 0)
{
return x_185;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_185, 0);
x_293 = lean_ctor_get(x_185, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_185);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
return x_294;
}
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_172);
lean_dec(x_5);
x_295 = lean_ctor_get(x_182, 0);
lean_inc(x_295);
lean_dec(x_182);
x_296 = lean_box(0);
x_297 = l_Lean_mkConst(x_295, x_296);
lean_inc(x_2);
lean_inc(x_297);
x_298 = l_Lean_Meta_inferType(x_297, x_2, x_159);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
lean_dec(x_298);
x_301 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__6___boxed), 6, 2);
lean_closure_set(x_301, 0, x_179);
lean_closure_set(x_301, 1, x_297);
x_302 = l_Lean_Meta_forallTelescope___rarg(x_299, x_301, x_2, x_300);
return x_302;
}
else
{
uint8_t x_303; 
lean_dec(x_297);
lean_dec(x_179);
lean_dec(x_2);
x_303 = !lean_is_exclusive(x_298);
if (x_303 == 0)
{
return x_298;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_298, 0);
x_305 = lean_ctor_get(x_298, 1);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_298);
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
return x_306;
}
}
}
}
else
{
lean_object* x_307; 
lean_dec(x_160);
x_307 = lean_box(0);
x_161 = x_307;
goto block_171;
}
block_171:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_161);
x_162 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_163 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_164 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_165 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_166 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_168 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_box(0);
x_170 = l_Lean_Meta_throwOther___rarg(x_168, x_169, x_2, x_159);
lean_dec(x_2);
return x_170;
}
}
case 3:
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_4, 1);
lean_inc(x_308);
lean_dec(x_4);
x_309 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_309) == 4)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_321 = lean_ctor_get(x_309, 0);
lean_inc(x_321);
lean_dec(x_309);
x_322 = lean_unsigned_to_nat(0u);
x_323 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_322);
x_324 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_323);
x_325 = lean_mk_array(x_323, x_324);
x_326 = lean_unsigned_to_nat(1u);
x_327 = lean_nat_sub(x_323, x_326);
lean_dec(x_323);
lean_inc(x_5);
x_328 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_325, x_327);
x_329 = lean_ctor_get(x_308, 0);
lean_inc(x_329);
x_330 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_331 = l_Lean_CombinatorCompilerAttribute_getDeclFor(x_330, x_329, x_321);
lean_dec(x_329);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
x_333 = l_Lean_Name_append___main(x_321, x_332);
lean_inc(x_321);
x_334 = l_Lean_Meta_getConstInfo(x_321, x_2, x_308);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec(x_334);
x_337 = l_Lean_ConstantInfo_type(x_335);
x_338 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_337);
x_339 = l_Lean_Meta_forallTelescope___rarg(x_337, x_338, x_2, x_336);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_411; uint8_t x_412; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec(x_339);
x_411 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8;
x_412 = l_Lean_Expr_isConstOf(x_340, x_411);
if (x_412 == 0)
{
lean_object* x_413; uint8_t x_414; 
x_413 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_414 = l_Lean_Expr_isConstOf(x_340, x_413);
lean_dec(x_340);
if (x_414 == 0)
{
lean_object* x_415; 
lean_dec(x_337);
lean_dec(x_335);
lean_dec(x_333);
lean_dec(x_328);
lean_dec(x_321);
lean_inc(x_2);
lean_inc(x_5);
x_415 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_341);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; 
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
lean_dec(x_415);
x_418 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_419 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_419, 0, x_418);
x_420 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_420, 0, x_419);
x_421 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__11;
x_422 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_420);
x_423 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_424 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_423);
x_425 = lean_box(0);
x_426 = l_Lean_Meta_throwOther___rarg(x_424, x_425, x_2, x_417);
lean_dec(x_2);
return x_426;
}
else
{
lean_object* x_427; lean_object* x_428; 
lean_dec(x_5);
x_427 = lean_ctor_get(x_415, 1);
lean_inc(x_427);
lean_dec(x_415);
x_428 = lean_ctor_get(x_416, 0);
lean_inc(x_428);
lean_dec(x_416);
x_1 = x_428;
x_3 = x_427;
goto _start;
}
}
else
{
uint8_t x_430; 
lean_dec(x_5);
lean_dec(x_2);
x_430 = !lean_is_exclusive(x_415);
if (x_430 == 0)
{
return x_415;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_415, 0);
x_432 = lean_ctor_get(x_415, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_415);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
return x_433;
}
}
}
else
{
lean_object* x_434; 
x_434 = lean_box(0);
x_342 = x_434;
goto block_410;
}
}
else
{
lean_object* x_435; 
lean_dec(x_340);
x_435 = lean_box(0);
x_342 = x_435;
goto block_410;
}
block_410:
{
lean_object* x_343; 
lean_dec(x_342);
x_343 = l_Lean_ConstantInfo_value_x3f(x_335);
lean_dec(x_335);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_337);
lean_dec(x_333);
lean_dec(x_328);
lean_dec(x_321);
x_344 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_345 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_345, 0, x_344);
x_346 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_346, 0, x_345);
x_347 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_348 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_346);
x_349 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_350 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
x_351 = lean_box(0);
x_352 = l_Lean_Meta_throwOther___rarg(x_350, x_351, x_2, x_341);
lean_dec(x_2);
return x_352;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_5);
x_353 = lean_ctor_get(x_343, 0);
lean_inc(x_353);
lean_dec(x_343);
x_354 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_353);
lean_inc(x_2);
x_355 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_354, x_2, x_341);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_376; lean_object* x_377; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
x_376 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__13;
lean_inc(x_2);
x_377 = l_Lean_Meta_forallTelescope___rarg(x_337, x_376, x_2, x_357);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
x_380 = lean_box(0);
lean_inc(x_333);
x_381 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_381, 0, x_333);
lean_ctor_set(x_381, 1, x_380);
lean_ctor_set(x_381, 2, x_378);
x_382 = lean_box(0);
x_383 = 0;
x_384 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_384, 0, x_381);
lean_ctor_set(x_384, 1, x_356);
lean_ctor_set(x_384, 2, x_382);
lean_ctor_set_uint8(x_384, sizeof(void*)*3, x_383);
x_385 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_385, 0, x_384);
x_386 = lean_ctor_get(x_379, 0);
lean_inc(x_386);
x_387 = l_Lean_Options_empty;
x_388 = l_Lean_Environment_addAndCompile(x_386, x_387, x_385);
lean_dec(x_385);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; 
lean_dec(x_333);
lean_dec(x_328);
lean_dec(x_321);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
lean_dec(x_388);
x_390 = l_Lean_KernelException_toMessageData(x_389, x_387);
x_391 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_390);
x_392 = l_Lean_Format_pretty(x_391, x_387);
x_393 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_393, 0, x_392);
x_394 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_394, 0, x_393);
x_395 = lean_box(0);
x_396 = l_Lean_Meta_throwOther___rarg(x_394, x_395, x_2, x_379);
lean_dec(x_2);
x_397 = !lean_is_exclusive(x_396);
if (x_397 == 0)
{
return x_396;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_396, 0);
x_399 = lean_ctor_get(x_396, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_396);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
else
{
lean_object* x_401; 
x_401 = lean_ctor_get(x_388, 0);
lean_inc(x_401);
lean_dec(x_388);
x_358 = x_401;
x_359 = x_379;
goto block_375;
}
}
else
{
uint8_t x_402; 
lean_dec(x_356);
lean_dec(x_333);
lean_dec(x_328);
lean_dec(x_321);
lean_dec(x_2);
x_402 = !lean_is_exclusive(x_377);
if (x_402 == 0)
{
return x_377;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_403 = lean_ctor_get(x_377, 0);
x_404 = lean_ctor_get(x_377, 1);
lean_inc(x_404);
lean_inc(x_403);
lean_dec(x_377);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_403);
lean_ctor_set(x_405, 1, x_404);
return x_405;
}
}
block_375:
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_inc(x_333);
x_360 = l_Lean_CombinatorCompilerAttribute_setDeclFor(x_330, x_358, x_321, x_333);
x_361 = l_Lean_Meta_setEnv(x_360, x_2, x_359);
x_362 = lean_ctor_get(x_361, 1);
lean_inc(x_362);
lean_dec(x_361);
x_363 = lean_box(0);
x_364 = l_Lean_mkConst(x_333, x_363);
lean_inc(x_2);
lean_inc(x_364);
x_365 = l_Lean_Meta_inferType(x_364, x_2, x_362);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_368 = l_Lean_mkAppStx___closed__2;
x_369 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__7___boxed), 8, 4);
lean_closure_set(x_369, 0, x_338);
lean_closure_set(x_369, 1, x_368);
lean_closure_set(x_369, 2, x_328);
lean_closure_set(x_369, 3, x_364);
x_370 = l_Lean_Meta_forallTelescope___rarg(x_366, x_369, x_2, x_367);
return x_370;
}
else
{
uint8_t x_371; 
lean_dec(x_364);
lean_dec(x_328);
lean_dec(x_2);
x_371 = !lean_is_exclusive(x_365);
if (x_371 == 0)
{
return x_365;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_365, 0);
x_373 = lean_ctor_get(x_365, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_365);
x_374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
return x_374;
}
}
}
}
else
{
uint8_t x_406; 
lean_dec(x_337);
lean_dec(x_333);
lean_dec(x_328);
lean_dec(x_321);
lean_dec(x_2);
x_406 = !lean_is_exclusive(x_355);
if (x_406 == 0)
{
return x_355;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_407 = lean_ctor_get(x_355, 0);
x_408 = lean_ctor_get(x_355, 1);
lean_inc(x_408);
lean_inc(x_407);
lean_dec(x_355);
x_409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
return x_409;
}
}
}
}
}
else
{
uint8_t x_436; 
lean_dec(x_337);
lean_dec(x_335);
lean_dec(x_333);
lean_dec(x_328);
lean_dec(x_321);
lean_dec(x_5);
lean_dec(x_2);
x_436 = !lean_is_exclusive(x_339);
if (x_436 == 0)
{
return x_339;
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_437 = lean_ctor_get(x_339, 0);
x_438 = lean_ctor_get(x_339, 1);
lean_inc(x_438);
lean_inc(x_437);
lean_dec(x_339);
x_439 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_439, 0, x_437);
lean_ctor_set(x_439, 1, x_438);
return x_439;
}
}
}
else
{
uint8_t x_440; 
lean_dec(x_333);
lean_dec(x_328);
lean_dec(x_321);
lean_dec(x_5);
lean_dec(x_2);
x_440 = !lean_is_exclusive(x_334);
if (x_440 == 0)
{
return x_334;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_334, 0);
x_442 = lean_ctor_get(x_334, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_334);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
return x_443;
}
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
lean_dec(x_321);
lean_dec(x_5);
x_444 = lean_ctor_get(x_331, 0);
lean_inc(x_444);
lean_dec(x_331);
x_445 = lean_box(0);
x_446 = l_Lean_mkConst(x_444, x_445);
lean_inc(x_2);
lean_inc(x_446);
x_447 = l_Lean_Meta_inferType(x_446, x_2, x_308);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_447, 1);
lean_inc(x_449);
lean_dec(x_447);
x_450 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__9___boxed), 6, 2);
lean_closure_set(x_450, 0, x_328);
lean_closure_set(x_450, 1, x_446);
x_451 = l_Lean_Meta_forallTelescope___rarg(x_448, x_450, x_2, x_449);
return x_451;
}
else
{
uint8_t x_452; 
lean_dec(x_446);
lean_dec(x_328);
lean_dec(x_2);
x_452 = !lean_is_exclusive(x_447);
if (x_452 == 0)
{
return x_447;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_447, 0);
x_454 = lean_ctor_get(x_447, 1);
lean_inc(x_454);
lean_inc(x_453);
lean_dec(x_447);
x_455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_455, 0, x_453);
lean_ctor_set(x_455, 1, x_454);
return x_455;
}
}
}
}
else
{
lean_object* x_456; 
lean_dec(x_309);
x_456 = lean_box(0);
x_310 = x_456;
goto block_320;
}
block_320:
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_310);
x_311 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_312 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_312, 0, x_311);
x_313 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_313, 0, x_312);
x_314 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_315 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_313);
x_316 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_317 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_box(0);
x_319 = l_Lean_Meta_throwOther___rarg(x_317, x_318, x_2, x_308);
lean_dec(x_2);
return x_319;
}
}
case 4:
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_4, 1);
lean_inc(x_457);
lean_dec(x_4);
x_458 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_458) == 4)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_470 = lean_ctor_get(x_458, 0);
lean_inc(x_470);
lean_dec(x_458);
x_471 = lean_unsigned_to_nat(0u);
x_472 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_471);
x_473 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_472);
x_474 = lean_mk_array(x_472, x_473);
x_475 = lean_unsigned_to_nat(1u);
x_476 = lean_nat_sub(x_472, x_475);
lean_dec(x_472);
lean_inc(x_5);
x_477 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_474, x_476);
x_478 = lean_ctor_get(x_457, 0);
lean_inc(x_478);
x_479 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_480 = l_Lean_CombinatorCompilerAttribute_getDeclFor(x_479, x_478, x_470);
lean_dec(x_478);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
x_482 = l_Lean_Name_append___main(x_470, x_481);
lean_inc(x_470);
x_483 = l_Lean_Meta_getConstInfo(x_470, x_2, x_457);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_484 = lean_ctor_get(x_483, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_483, 1);
lean_inc(x_485);
lean_dec(x_483);
x_486 = l_Lean_ConstantInfo_type(x_484);
x_487 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_486);
x_488 = l_Lean_Meta_forallTelescope___rarg(x_486, x_487, x_2, x_485);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_560; uint8_t x_561; 
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_488, 1);
lean_inc(x_490);
lean_dec(x_488);
x_560 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8;
x_561 = l_Lean_Expr_isConstOf(x_489, x_560);
if (x_561 == 0)
{
lean_object* x_562; uint8_t x_563; 
x_562 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_563 = l_Lean_Expr_isConstOf(x_489, x_562);
lean_dec(x_489);
if (x_563 == 0)
{
lean_object* x_564; 
lean_dec(x_486);
lean_dec(x_484);
lean_dec(x_482);
lean_dec(x_477);
lean_dec(x_470);
lean_inc(x_2);
lean_inc(x_5);
x_564 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_490);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; 
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
if (lean_obj_tag(x_565) == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_566 = lean_ctor_get(x_564, 1);
lean_inc(x_566);
lean_dec(x_564);
x_567 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_568 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_568, 0, x_567);
x_569 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_569, 0, x_568);
x_570 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__11;
x_571 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_571, 0, x_570);
lean_ctor_set(x_571, 1, x_569);
x_572 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_573 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_573, 0, x_571);
lean_ctor_set(x_573, 1, x_572);
x_574 = lean_box(0);
x_575 = l_Lean_Meta_throwOther___rarg(x_573, x_574, x_2, x_566);
lean_dec(x_2);
return x_575;
}
else
{
lean_object* x_576; lean_object* x_577; 
lean_dec(x_5);
x_576 = lean_ctor_get(x_564, 1);
lean_inc(x_576);
lean_dec(x_564);
x_577 = lean_ctor_get(x_565, 0);
lean_inc(x_577);
lean_dec(x_565);
x_1 = x_577;
x_3 = x_576;
goto _start;
}
}
else
{
uint8_t x_579; 
lean_dec(x_5);
lean_dec(x_2);
x_579 = !lean_is_exclusive(x_564);
if (x_579 == 0)
{
return x_564;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_580 = lean_ctor_get(x_564, 0);
x_581 = lean_ctor_get(x_564, 1);
lean_inc(x_581);
lean_inc(x_580);
lean_dec(x_564);
x_582 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_582, 0, x_580);
lean_ctor_set(x_582, 1, x_581);
return x_582;
}
}
}
else
{
lean_object* x_583; 
x_583 = lean_box(0);
x_491 = x_583;
goto block_559;
}
}
else
{
lean_object* x_584; 
lean_dec(x_489);
x_584 = lean_box(0);
x_491 = x_584;
goto block_559;
}
block_559:
{
lean_object* x_492; 
lean_dec(x_491);
x_492 = l_Lean_ConstantInfo_value_x3f(x_484);
lean_dec(x_484);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
lean_dec(x_486);
lean_dec(x_482);
lean_dec(x_477);
lean_dec(x_470);
x_493 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_494 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_494, 0, x_493);
x_495 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_495, 0, x_494);
x_496 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_497 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_497, 0, x_496);
lean_ctor_set(x_497, 1, x_495);
x_498 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_499 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_499, 0, x_497);
lean_ctor_set(x_499, 1, x_498);
x_500 = lean_box(0);
x_501 = l_Lean_Meta_throwOther___rarg(x_499, x_500, x_2, x_490);
lean_dec(x_2);
return x_501;
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; 
lean_dec(x_5);
x_502 = lean_ctor_get(x_492, 0);
lean_inc(x_502);
lean_dec(x_492);
x_503 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_502);
lean_inc(x_2);
x_504 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_503, x_2, x_490);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_525; lean_object* x_526; 
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_504, 1);
lean_inc(x_506);
lean_dec(x_504);
x_525 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__14;
lean_inc(x_2);
x_526 = l_Lean_Meta_forallTelescope___rarg(x_486, x_525, x_2, x_506);
if (lean_obj_tag(x_526) == 0)
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; uint8_t x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_526, 1);
lean_inc(x_528);
lean_dec(x_526);
x_529 = lean_box(0);
lean_inc(x_482);
x_530 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_530, 0, x_482);
lean_ctor_set(x_530, 1, x_529);
lean_ctor_set(x_530, 2, x_527);
x_531 = lean_box(0);
x_532 = 0;
x_533 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_533, 0, x_530);
lean_ctor_set(x_533, 1, x_505);
lean_ctor_set(x_533, 2, x_531);
lean_ctor_set_uint8(x_533, sizeof(void*)*3, x_532);
x_534 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_534, 0, x_533);
x_535 = lean_ctor_get(x_528, 0);
lean_inc(x_535);
x_536 = l_Lean_Options_empty;
x_537 = l_Lean_Environment_addAndCompile(x_535, x_536, x_534);
lean_dec(x_534);
if (lean_obj_tag(x_537) == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; uint8_t x_546; 
lean_dec(x_482);
lean_dec(x_477);
lean_dec(x_470);
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
lean_dec(x_537);
x_539 = l_Lean_KernelException_toMessageData(x_538, x_536);
x_540 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_539);
x_541 = l_Lean_Format_pretty(x_540, x_536);
x_542 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_542, 0, x_541);
x_543 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_543, 0, x_542);
x_544 = lean_box(0);
x_545 = l_Lean_Meta_throwOther___rarg(x_543, x_544, x_2, x_528);
lean_dec(x_2);
x_546 = !lean_is_exclusive(x_545);
if (x_546 == 0)
{
return x_545;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_547 = lean_ctor_get(x_545, 0);
x_548 = lean_ctor_get(x_545, 1);
lean_inc(x_548);
lean_inc(x_547);
lean_dec(x_545);
x_549 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_549, 0, x_547);
lean_ctor_set(x_549, 1, x_548);
return x_549;
}
}
else
{
lean_object* x_550; 
x_550 = lean_ctor_get(x_537, 0);
lean_inc(x_550);
lean_dec(x_537);
x_507 = x_550;
x_508 = x_528;
goto block_524;
}
}
else
{
uint8_t x_551; 
lean_dec(x_505);
lean_dec(x_482);
lean_dec(x_477);
lean_dec(x_470);
lean_dec(x_2);
x_551 = !lean_is_exclusive(x_526);
if (x_551 == 0)
{
return x_526;
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_552 = lean_ctor_get(x_526, 0);
x_553 = lean_ctor_get(x_526, 1);
lean_inc(x_553);
lean_inc(x_552);
lean_dec(x_526);
x_554 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_554, 0, x_552);
lean_ctor_set(x_554, 1, x_553);
return x_554;
}
}
block_524:
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
lean_inc(x_482);
x_509 = l_Lean_CombinatorCompilerAttribute_setDeclFor(x_479, x_507, x_470, x_482);
x_510 = l_Lean_Meta_setEnv(x_509, x_2, x_508);
x_511 = lean_ctor_get(x_510, 1);
lean_inc(x_511);
lean_dec(x_510);
x_512 = lean_box(0);
x_513 = l_Lean_mkConst(x_482, x_512);
lean_inc(x_2);
lean_inc(x_513);
x_514 = l_Lean_Meta_inferType(x_513, x_2, x_511);
if (lean_obj_tag(x_514) == 0)
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_514, 1);
lean_inc(x_516);
lean_dec(x_514);
x_517 = l_Lean_mkAppStx___closed__2;
x_518 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__10___boxed), 8, 4);
lean_closure_set(x_518, 0, x_487);
lean_closure_set(x_518, 1, x_517);
lean_closure_set(x_518, 2, x_477);
lean_closure_set(x_518, 3, x_513);
x_519 = l_Lean_Meta_forallTelescope___rarg(x_515, x_518, x_2, x_516);
return x_519;
}
else
{
uint8_t x_520; 
lean_dec(x_513);
lean_dec(x_477);
lean_dec(x_2);
x_520 = !lean_is_exclusive(x_514);
if (x_520 == 0)
{
return x_514;
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_521 = lean_ctor_get(x_514, 0);
x_522 = lean_ctor_get(x_514, 1);
lean_inc(x_522);
lean_inc(x_521);
lean_dec(x_514);
x_523 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_523, 0, x_521);
lean_ctor_set(x_523, 1, x_522);
return x_523;
}
}
}
}
else
{
uint8_t x_555; 
lean_dec(x_486);
lean_dec(x_482);
lean_dec(x_477);
lean_dec(x_470);
lean_dec(x_2);
x_555 = !lean_is_exclusive(x_504);
if (x_555 == 0)
{
return x_504;
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_556 = lean_ctor_get(x_504, 0);
x_557 = lean_ctor_get(x_504, 1);
lean_inc(x_557);
lean_inc(x_556);
lean_dec(x_504);
x_558 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_558, 0, x_556);
lean_ctor_set(x_558, 1, x_557);
return x_558;
}
}
}
}
}
else
{
uint8_t x_585; 
lean_dec(x_486);
lean_dec(x_484);
lean_dec(x_482);
lean_dec(x_477);
lean_dec(x_470);
lean_dec(x_5);
lean_dec(x_2);
x_585 = !lean_is_exclusive(x_488);
if (x_585 == 0)
{
return x_488;
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_586 = lean_ctor_get(x_488, 0);
x_587 = lean_ctor_get(x_488, 1);
lean_inc(x_587);
lean_inc(x_586);
lean_dec(x_488);
x_588 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_588, 0, x_586);
lean_ctor_set(x_588, 1, x_587);
return x_588;
}
}
}
else
{
uint8_t x_589; 
lean_dec(x_482);
lean_dec(x_477);
lean_dec(x_470);
lean_dec(x_5);
lean_dec(x_2);
x_589 = !lean_is_exclusive(x_483);
if (x_589 == 0)
{
return x_483;
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_590 = lean_ctor_get(x_483, 0);
x_591 = lean_ctor_get(x_483, 1);
lean_inc(x_591);
lean_inc(x_590);
lean_dec(x_483);
x_592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_591);
return x_592;
}
}
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
lean_dec(x_470);
lean_dec(x_5);
x_593 = lean_ctor_get(x_480, 0);
lean_inc(x_593);
lean_dec(x_480);
x_594 = lean_box(0);
x_595 = l_Lean_mkConst(x_593, x_594);
lean_inc(x_2);
lean_inc(x_595);
x_596 = l_Lean_Meta_inferType(x_595, x_2, x_457);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_597 = lean_ctor_get(x_596, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_596, 1);
lean_inc(x_598);
lean_dec(x_596);
x_599 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__12___boxed), 6, 2);
lean_closure_set(x_599, 0, x_477);
lean_closure_set(x_599, 1, x_595);
x_600 = l_Lean_Meta_forallTelescope___rarg(x_597, x_599, x_2, x_598);
return x_600;
}
else
{
uint8_t x_601; 
lean_dec(x_595);
lean_dec(x_477);
lean_dec(x_2);
x_601 = !lean_is_exclusive(x_596);
if (x_601 == 0)
{
return x_596;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_602 = lean_ctor_get(x_596, 0);
x_603 = lean_ctor_get(x_596, 1);
lean_inc(x_603);
lean_inc(x_602);
lean_dec(x_596);
x_604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_604, 0, x_602);
lean_ctor_set(x_604, 1, x_603);
return x_604;
}
}
}
}
else
{
lean_object* x_605; 
lean_dec(x_458);
x_605 = lean_box(0);
x_459 = x_605;
goto block_469;
}
block_469:
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
lean_dec(x_459);
x_460 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_461 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_461, 0, x_460);
x_462 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_462, 0, x_461);
x_463 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_464 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_462);
x_465 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_466 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
x_467 = lean_box(0);
x_468 = l_Lean_Meta_throwOther___rarg(x_466, x_467, x_2, x_457);
lean_dec(x_2);
return x_468;
}
}
case 5:
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_606 = lean_ctor_get(x_4, 1);
lean_inc(x_606);
lean_dec(x_4);
x_607 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_607) == 4)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
x_619 = lean_ctor_get(x_607, 0);
lean_inc(x_619);
lean_dec(x_607);
x_620 = lean_unsigned_to_nat(0u);
x_621 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_620);
x_622 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_621);
x_623 = lean_mk_array(x_621, x_622);
x_624 = lean_unsigned_to_nat(1u);
x_625 = lean_nat_sub(x_621, x_624);
lean_dec(x_621);
lean_inc(x_5);
x_626 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_623, x_625);
x_627 = lean_ctor_get(x_606, 0);
lean_inc(x_627);
x_628 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_629 = l_Lean_CombinatorCompilerAttribute_getDeclFor(x_628, x_627, x_619);
lean_dec(x_627);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_630 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
x_631 = l_Lean_Name_append___main(x_619, x_630);
lean_inc(x_619);
x_632 = l_Lean_Meta_getConstInfo(x_619, x_2, x_606);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_634);
lean_dec(x_632);
x_635 = l_Lean_ConstantInfo_type(x_633);
x_636 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_635);
x_637 = l_Lean_Meta_forallTelescope___rarg(x_635, x_636, x_2, x_634);
if (lean_obj_tag(x_637) == 0)
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_709; uint8_t x_710; 
x_638 = lean_ctor_get(x_637, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_637, 1);
lean_inc(x_639);
lean_dec(x_637);
x_709 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8;
x_710 = l_Lean_Expr_isConstOf(x_638, x_709);
if (x_710 == 0)
{
lean_object* x_711; uint8_t x_712; 
x_711 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_712 = l_Lean_Expr_isConstOf(x_638, x_711);
lean_dec(x_638);
if (x_712 == 0)
{
lean_object* x_713; 
lean_dec(x_635);
lean_dec(x_633);
lean_dec(x_631);
lean_dec(x_626);
lean_dec(x_619);
lean_inc(x_2);
lean_inc(x_5);
x_713 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_639);
if (lean_obj_tag(x_713) == 0)
{
lean_object* x_714; 
x_714 = lean_ctor_get(x_713, 0);
lean_inc(x_714);
if (lean_obj_tag(x_714) == 0)
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_715 = lean_ctor_get(x_713, 1);
lean_inc(x_715);
lean_dec(x_713);
x_716 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_717 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_717, 0, x_716);
x_718 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_718, 0, x_717);
x_719 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__11;
x_720 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_720, 0, x_719);
lean_ctor_set(x_720, 1, x_718);
x_721 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_722 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_722, 0, x_720);
lean_ctor_set(x_722, 1, x_721);
x_723 = lean_box(0);
x_724 = l_Lean_Meta_throwOther___rarg(x_722, x_723, x_2, x_715);
lean_dec(x_2);
return x_724;
}
else
{
lean_object* x_725; lean_object* x_726; 
lean_dec(x_5);
x_725 = lean_ctor_get(x_713, 1);
lean_inc(x_725);
lean_dec(x_713);
x_726 = lean_ctor_get(x_714, 0);
lean_inc(x_726);
lean_dec(x_714);
x_1 = x_726;
x_3 = x_725;
goto _start;
}
}
else
{
uint8_t x_728; 
lean_dec(x_5);
lean_dec(x_2);
x_728 = !lean_is_exclusive(x_713);
if (x_728 == 0)
{
return x_713;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_729 = lean_ctor_get(x_713, 0);
x_730 = lean_ctor_get(x_713, 1);
lean_inc(x_730);
lean_inc(x_729);
lean_dec(x_713);
x_731 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_731, 0, x_729);
lean_ctor_set(x_731, 1, x_730);
return x_731;
}
}
}
else
{
lean_object* x_732; 
x_732 = lean_box(0);
x_640 = x_732;
goto block_708;
}
}
else
{
lean_object* x_733; 
lean_dec(x_638);
x_733 = lean_box(0);
x_640 = x_733;
goto block_708;
}
block_708:
{
lean_object* x_641; 
lean_dec(x_640);
x_641 = l_Lean_ConstantInfo_value_x3f(x_633);
lean_dec(x_633);
if (lean_obj_tag(x_641) == 0)
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; 
lean_dec(x_635);
lean_dec(x_631);
lean_dec(x_626);
lean_dec(x_619);
x_642 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_643 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_643, 0, x_642);
x_644 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_644, 0, x_643);
x_645 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_646 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_646, 0, x_645);
lean_ctor_set(x_646, 1, x_644);
x_647 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_648 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_648, 0, x_646);
lean_ctor_set(x_648, 1, x_647);
x_649 = lean_box(0);
x_650 = l_Lean_Meta_throwOther___rarg(x_648, x_649, x_2, x_639);
lean_dec(x_2);
return x_650;
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_5);
x_651 = lean_ctor_get(x_641, 0);
lean_inc(x_651);
lean_dec(x_641);
x_652 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_651);
lean_inc(x_2);
x_653 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_652, x_2, x_639);
if (lean_obj_tag(x_653) == 0)
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_674; lean_object* x_675; 
x_654 = lean_ctor_get(x_653, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_653, 1);
lean_inc(x_655);
lean_dec(x_653);
x_674 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__15;
lean_inc(x_2);
x_675 = l_Lean_Meta_forallTelescope___rarg(x_635, x_674, x_2, x_655);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; uint8_t x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
x_676 = lean_ctor_get(x_675, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_675, 1);
lean_inc(x_677);
lean_dec(x_675);
x_678 = lean_box(0);
lean_inc(x_631);
x_679 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_679, 0, x_631);
lean_ctor_set(x_679, 1, x_678);
lean_ctor_set(x_679, 2, x_676);
x_680 = lean_box(0);
x_681 = 0;
x_682 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_682, 0, x_679);
lean_ctor_set(x_682, 1, x_654);
lean_ctor_set(x_682, 2, x_680);
lean_ctor_set_uint8(x_682, sizeof(void*)*3, x_681);
x_683 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_683, 0, x_682);
x_684 = lean_ctor_get(x_677, 0);
lean_inc(x_684);
x_685 = l_Lean_Options_empty;
x_686 = l_Lean_Environment_addAndCompile(x_684, x_685, x_683);
lean_dec(x_683);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; uint8_t x_695; 
lean_dec(x_631);
lean_dec(x_626);
lean_dec(x_619);
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
lean_dec(x_686);
x_688 = l_Lean_KernelException_toMessageData(x_687, x_685);
x_689 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_688);
x_690 = l_Lean_Format_pretty(x_689, x_685);
x_691 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_691, 0, x_690);
x_692 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_692, 0, x_691);
x_693 = lean_box(0);
x_694 = l_Lean_Meta_throwOther___rarg(x_692, x_693, x_2, x_677);
lean_dec(x_2);
x_695 = !lean_is_exclusive(x_694);
if (x_695 == 0)
{
return x_694;
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_696 = lean_ctor_get(x_694, 0);
x_697 = lean_ctor_get(x_694, 1);
lean_inc(x_697);
lean_inc(x_696);
lean_dec(x_694);
x_698 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_698, 0, x_696);
lean_ctor_set(x_698, 1, x_697);
return x_698;
}
}
else
{
lean_object* x_699; 
x_699 = lean_ctor_get(x_686, 0);
lean_inc(x_699);
lean_dec(x_686);
x_656 = x_699;
x_657 = x_677;
goto block_673;
}
}
else
{
uint8_t x_700; 
lean_dec(x_654);
lean_dec(x_631);
lean_dec(x_626);
lean_dec(x_619);
lean_dec(x_2);
x_700 = !lean_is_exclusive(x_675);
if (x_700 == 0)
{
return x_675;
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; 
x_701 = lean_ctor_get(x_675, 0);
x_702 = lean_ctor_get(x_675, 1);
lean_inc(x_702);
lean_inc(x_701);
lean_dec(x_675);
x_703 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_703, 0, x_701);
lean_ctor_set(x_703, 1, x_702);
return x_703;
}
}
block_673:
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
lean_inc(x_631);
x_658 = l_Lean_CombinatorCompilerAttribute_setDeclFor(x_628, x_656, x_619, x_631);
x_659 = l_Lean_Meta_setEnv(x_658, x_2, x_657);
x_660 = lean_ctor_get(x_659, 1);
lean_inc(x_660);
lean_dec(x_659);
x_661 = lean_box(0);
x_662 = l_Lean_mkConst(x_631, x_661);
lean_inc(x_2);
lean_inc(x_662);
x_663 = l_Lean_Meta_inferType(x_662, x_2, x_660);
if (lean_obj_tag(x_663) == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_663, 1);
lean_inc(x_665);
lean_dec(x_663);
x_666 = l_Lean_mkAppStx___closed__2;
x_667 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__13___boxed), 8, 4);
lean_closure_set(x_667, 0, x_636);
lean_closure_set(x_667, 1, x_666);
lean_closure_set(x_667, 2, x_626);
lean_closure_set(x_667, 3, x_662);
x_668 = l_Lean_Meta_forallTelescope___rarg(x_664, x_667, x_2, x_665);
return x_668;
}
else
{
uint8_t x_669; 
lean_dec(x_662);
lean_dec(x_626);
lean_dec(x_2);
x_669 = !lean_is_exclusive(x_663);
if (x_669 == 0)
{
return x_663;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_670 = lean_ctor_get(x_663, 0);
x_671 = lean_ctor_get(x_663, 1);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_663);
x_672 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_672, 0, x_670);
lean_ctor_set(x_672, 1, x_671);
return x_672;
}
}
}
}
else
{
uint8_t x_704; 
lean_dec(x_635);
lean_dec(x_631);
lean_dec(x_626);
lean_dec(x_619);
lean_dec(x_2);
x_704 = !lean_is_exclusive(x_653);
if (x_704 == 0)
{
return x_653;
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_705 = lean_ctor_get(x_653, 0);
x_706 = lean_ctor_get(x_653, 1);
lean_inc(x_706);
lean_inc(x_705);
lean_dec(x_653);
x_707 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_707, 0, x_705);
lean_ctor_set(x_707, 1, x_706);
return x_707;
}
}
}
}
}
else
{
uint8_t x_734; 
lean_dec(x_635);
lean_dec(x_633);
lean_dec(x_631);
lean_dec(x_626);
lean_dec(x_619);
lean_dec(x_5);
lean_dec(x_2);
x_734 = !lean_is_exclusive(x_637);
if (x_734 == 0)
{
return x_637;
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; 
x_735 = lean_ctor_get(x_637, 0);
x_736 = lean_ctor_get(x_637, 1);
lean_inc(x_736);
lean_inc(x_735);
lean_dec(x_637);
x_737 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_737, 0, x_735);
lean_ctor_set(x_737, 1, x_736);
return x_737;
}
}
}
else
{
uint8_t x_738; 
lean_dec(x_631);
lean_dec(x_626);
lean_dec(x_619);
lean_dec(x_5);
lean_dec(x_2);
x_738 = !lean_is_exclusive(x_632);
if (x_738 == 0)
{
return x_632;
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; 
x_739 = lean_ctor_get(x_632, 0);
x_740 = lean_ctor_get(x_632, 1);
lean_inc(x_740);
lean_inc(x_739);
lean_dec(x_632);
x_741 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_741, 0, x_739);
lean_ctor_set(x_741, 1, x_740);
return x_741;
}
}
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
lean_dec(x_619);
lean_dec(x_5);
x_742 = lean_ctor_get(x_629, 0);
lean_inc(x_742);
lean_dec(x_629);
x_743 = lean_box(0);
x_744 = l_Lean_mkConst(x_742, x_743);
lean_inc(x_2);
lean_inc(x_744);
x_745 = l_Lean_Meta_inferType(x_744, x_2, x_606);
if (lean_obj_tag(x_745) == 0)
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
x_746 = lean_ctor_get(x_745, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_745, 1);
lean_inc(x_747);
lean_dec(x_745);
x_748 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__15___boxed), 6, 2);
lean_closure_set(x_748, 0, x_626);
lean_closure_set(x_748, 1, x_744);
x_749 = l_Lean_Meta_forallTelescope___rarg(x_746, x_748, x_2, x_747);
return x_749;
}
else
{
uint8_t x_750; 
lean_dec(x_744);
lean_dec(x_626);
lean_dec(x_2);
x_750 = !lean_is_exclusive(x_745);
if (x_750 == 0)
{
return x_745;
}
else
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_751 = lean_ctor_get(x_745, 0);
x_752 = lean_ctor_get(x_745, 1);
lean_inc(x_752);
lean_inc(x_751);
lean_dec(x_745);
x_753 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_753, 0, x_751);
lean_ctor_set(x_753, 1, x_752);
return x_753;
}
}
}
}
else
{
lean_object* x_754; 
lean_dec(x_607);
x_754 = lean_box(0);
x_608 = x_754;
goto block_618;
}
block_618:
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
lean_dec(x_608);
x_609 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_610 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_610, 0, x_609);
x_611 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_611, 0, x_610);
x_612 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_613 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_613, 0, x_612);
lean_ctor_set(x_613, 1, x_611);
x_614 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_615 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_615, 0, x_613);
lean_ctor_set(x_615, 1, x_614);
x_616 = lean_box(0);
x_617 = l_Lean_Meta_throwOther___rarg(x_615, x_616, x_2, x_606);
lean_dec(x_2);
return x_617;
}
}
case 6:
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; 
x_755 = lean_ctor_get(x_4, 1);
lean_inc(x_755);
lean_dec(x_4);
x_756 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__16;
x_757 = l_Lean_Meta_lambdaTelescope___rarg(x_5, x_756, x_2, x_755);
return x_757;
}
case 7:
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; 
x_758 = lean_ctor_get(x_4, 1);
lean_inc(x_758);
lean_dec(x_4);
x_759 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_759) == 4)
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; 
x_771 = lean_ctor_get(x_759, 0);
lean_inc(x_771);
lean_dec(x_759);
x_772 = lean_unsigned_to_nat(0u);
x_773 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_772);
x_774 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_773);
x_775 = lean_mk_array(x_773, x_774);
x_776 = lean_unsigned_to_nat(1u);
x_777 = lean_nat_sub(x_773, x_776);
lean_dec(x_773);
lean_inc(x_5);
x_778 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_775, x_777);
x_779 = lean_ctor_get(x_758, 0);
lean_inc(x_779);
x_780 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_781 = l_Lean_CombinatorCompilerAttribute_getDeclFor(x_780, x_779, x_771);
lean_dec(x_779);
if (lean_obj_tag(x_781) == 0)
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; 
x_782 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
x_783 = l_Lean_Name_append___main(x_771, x_782);
lean_inc(x_771);
x_784 = l_Lean_Meta_getConstInfo(x_771, x_2, x_758);
if (lean_obj_tag(x_784) == 0)
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; 
x_785 = lean_ctor_get(x_784, 0);
lean_inc(x_785);
x_786 = lean_ctor_get(x_784, 1);
lean_inc(x_786);
lean_dec(x_784);
x_787 = l_Lean_ConstantInfo_type(x_785);
x_788 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_787);
x_789 = l_Lean_Meta_forallTelescope___rarg(x_787, x_788, x_2, x_786);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_861; uint8_t x_862; 
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
lean_dec(x_789);
x_861 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8;
x_862 = l_Lean_Expr_isConstOf(x_790, x_861);
if (x_862 == 0)
{
lean_object* x_863; uint8_t x_864; 
x_863 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_864 = l_Lean_Expr_isConstOf(x_790, x_863);
lean_dec(x_790);
if (x_864 == 0)
{
lean_object* x_865; 
lean_dec(x_787);
lean_dec(x_785);
lean_dec(x_783);
lean_dec(x_778);
lean_dec(x_771);
lean_inc(x_2);
lean_inc(x_5);
x_865 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_791);
if (lean_obj_tag(x_865) == 0)
{
lean_object* x_866; 
x_866 = lean_ctor_get(x_865, 0);
lean_inc(x_866);
if (lean_obj_tag(x_866) == 0)
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; 
x_867 = lean_ctor_get(x_865, 1);
lean_inc(x_867);
lean_dec(x_865);
x_868 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_869 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_869, 0, x_868);
x_870 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_870, 0, x_869);
x_871 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__11;
x_872 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_872, 0, x_871);
lean_ctor_set(x_872, 1, x_870);
x_873 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_874 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_874, 0, x_872);
lean_ctor_set(x_874, 1, x_873);
x_875 = lean_box(0);
x_876 = l_Lean_Meta_throwOther___rarg(x_874, x_875, x_2, x_867);
lean_dec(x_2);
return x_876;
}
else
{
lean_object* x_877; lean_object* x_878; 
lean_dec(x_5);
x_877 = lean_ctor_get(x_865, 1);
lean_inc(x_877);
lean_dec(x_865);
x_878 = lean_ctor_get(x_866, 0);
lean_inc(x_878);
lean_dec(x_866);
x_1 = x_878;
x_3 = x_877;
goto _start;
}
}
else
{
uint8_t x_880; 
lean_dec(x_5);
lean_dec(x_2);
x_880 = !lean_is_exclusive(x_865);
if (x_880 == 0)
{
return x_865;
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_881 = lean_ctor_get(x_865, 0);
x_882 = lean_ctor_get(x_865, 1);
lean_inc(x_882);
lean_inc(x_881);
lean_dec(x_865);
x_883 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_883, 0, x_881);
lean_ctor_set(x_883, 1, x_882);
return x_883;
}
}
}
else
{
lean_object* x_884; 
x_884 = lean_box(0);
x_792 = x_884;
goto block_860;
}
}
else
{
lean_object* x_885; 
lean_dec(x_790);
x_885 = lean_box(0);
x_792 = x_885;
goto block_860;
}
block_860:
{
lean_object* x_793; 
lean_dec(x_792);
x_793 = l_Lean_ConstantInfo_value_x3f(x_785);
lean_dec(x_785);
if (lean_obj_tag(x_793) == 0)
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; 
lean_dec(x_787);
lean_dec(x_783);
lean_dec(x_778);
lean_dec(x_771);
x_794 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_795 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_795, 0, x_794);
x_796 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_796, 0, x_795);
x_797 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_798 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_798, 0, x_797);
lean_ctor_set(x_798, 1, x_796);
x_799 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_800 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_800, 0, x_798);
lean_ctor_set(x_800, 1, x_799);
x_801 = lean_box(0);
x_802 = l_Lean_Meta_throwOther___rarg(x_800, x_801, x_2, x_791);
lean_dec(x_2);
return x_802;
}
else
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; 
lean_dec(x_5);
x_803 = lean_ctor_get(x_793, 0);
lean_inc(x_803);
lean_dec(x_793);
x_804 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_803);
lean_inc(x_2);
x_805 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_804, x_2, x_791);
if (lean_obj_tag(x_805) == 0)
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_826; lean_object* x_827; 
x_806 = lean_ctor_get(x_805, 0);
lean_inc(x_806);
x_807 = lean_ctor_get(x_805, 1);
lean_inc(x_807);
lean_dec(x_805);
x_826 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__17;
lean_inc(x_2);
x_827 = l_Lean_Meta_forallTelescope___rarg(x_787, x_826, x_2, x_807);
if (lean_obj_tag(x_827) == 0)
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; uint8_t x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; 
x_828 = lean_ctor_get(x_827, 0);
lean_inc(x_828);
x_829 = lean_ctor_get(x_827, 1);
lean_inc(x_829);
lean_dec(x_827);
x_830 = lean_box(0);
lean_inc(x_783);
x_831 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_831, 0, x_783);
lean_ctor_set(x_831, 1, x_830);
lean_ctor_set(x_831, 2, x_828);
x_832 = lean_box(0);
x_833 = 0;
x_834 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_834, 0, x_831);
lean_ctor_set(x_834, 1, x_806);
lean_ctor_set(x_834, 2, x_832);
lean_ctor_set_uint8(x_834, sizeof(void*)*3, x_833);
x_835 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_835, 0, x_834);
x_836 = lean_ctor_get(x_829, 0);
lean_inc(x_836);
x_837 = l_Lean_Options_empty;
x_838 = l_Lean_Environment_addAndCompile(x_836, x_837, x_835);
lean_dec(x_835);
if (lean_obj_tag(x_838) == 0)
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; uint8_t x_847; 
lean_dec(x_783);
lean_dec(x_778);
lean_dec(x_771);
x_839 = lean_ctor_get(x_838, 0);
lean_inc(x_839);
lean_dec(x_838);
x_840 = l_Lean_KernelException_toMessageData(x_839, x_837);
x_841 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_840);
x_842 = l_Lean_Format_pretty(x_841, x_837);
x_843 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_843, 0, x_842);
x_844 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_844, 0, x_843);
x_845 = lean_box(0);
x_846 = l_Lean_Meta_throwOther___rarg(x_844, x_845, x_2, x_829);
lean_dec(x_2);
x_847 = !lean_is_exclusive(x_846);
if (x_847 == 0)
{
return x_846;
}
else
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; 
x_848 = lean_ctor_get(x_846, 0);
x_849 = lean_ctor_get(x_846, 1);
lean_inc(x_849);
lean_inc(x_848);
lean_dec(x_846);
x_850 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_850, 0, x_848);
lean_ctor_set(x_850, 1, x_849);
return x_850;
}
}
else
{
lean_object* x_851; 
x_851 = lean_ctor_get(x_838, 0);
lean_inc(x_851);
lean_dec(x_838);
x_808 = x_851;
x_809 = x_829;
goto block_825;
}
}
else
{
uint8_t x_852; 
lean_dec(x_806);
lean_dec(x_783);
lean_dec(x_778);
lean_dec(x_771);
lean_dec(x_2);
x_852 = !lean_is_exclusive(x_827);
if (x_852 == 0)
{
return x_827;
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; 
x_853 = lean_ctor_get(x_827, 0);
x_854 = lean_ctor_get(x_827, 1);
lean_inc(x_854);
lean_inc(x_853);
lean_dec(x_827);
x_855 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_855, 0, x_853);
lean_ctor_set(x_855, 1, x_854);
return x_855;
}
}
block_825:
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; 
lean_inc(x_783);
x_810 = l_Lean_CombinatorCompilerAttribute_setDeclFor(x_780, x_808, x_771, x_783);
x_811 = l_Lean_Meta_setEnv(x_810, x_2, x_809);
x_812 = lean_ctor_get(x_811, 1);
lean_inc(x_812);
lean_dec(x_811);
x_813 = lean_box(0);
x_814 = l_Lean_mkConst(x_783, x_813);
lean_inc(x_2);
lean_inc(x_814);
x_815 = l_Lean_Meta_inferType(x_814, x_2, x_812);
if (lean_obj_tag(x_815) == 0)
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; 
x_816 = lean_ctor_get(x_815, 0);
lean_inc(x_816);
x_817 = lean_ctor_get(x_815, 1);
lean_inc(x_817);
lean_dec(x_815);
x_818 = l_Lean_mkAppStx___closed__2;
x_819 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__17___boxed), 8, 4);
lean_closure_set(x_819, 0, x_788);
lean_closure_set(x_819, 1, x_818);
lean_closure_set(x_819, 2, x_778);
lean_closure_set(x_819, 3, x_814);
x_820 = l_Lean_Meta_forallTelescope___rarg(x_816, x_819, x_2, x_817);
return x_820;
}
else
{
uint8_t x_821; 
lean_dec(x_814);
lean_dec(x_778);
lean_dec(x_2);
x_821 = !lean_is_exclusive(x_815);
if (x_821 == 0)
{
return x_815;
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_822 = lean_ctor_get(x_815, 0);
x_823 = lean_ctor_get(x_815, 1);
lean_inc(x_823);
lean_inc(x_822);
lean_dec(x_815);
x_824 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_824, 0, x_822);
lean_ctor_set(x_824, 1, x_823);
return x_824;
}
}
}
}
else
{
uint8_t x_856; 
lean_dec(x_787);
lean_dec(x_783);
lean_dec(x_778);
lean_dec(x_771);
lean_dec(x_2);
x_856 = !lean_is_exclusive(x_805);
if (x_856 == 0)
{
return x_805;
}
else
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; 
x_857 = lean_ctor_get(x_805, 0);
x_858 = lean_ctor_get(x_805, 1);
lean_inc(x_858);
lean_inc(x_857);
lean_dec(x_805);
x_859 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_859, 0, x_857);
lean_ctor_set(x_859, 1, x_858);
return x_859;
}
}
}
}
}
else
{
uint8_t x_886; 
lean_dec(x_787);
lean_dec(x_785);
lean_dec(x_783);
lean_dec(x_778);
lean_dec(x_771);
lean_dec(x_5);
lean_dec(x_2);
x_886 = !lean_is_exclusive(x_789);
if (x_886 == 0)
{
return x_789;
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; 
x_887 = lean_ctor_get(x_789, 0);
x_888 = lean_ctor_get(x_789, 1);
lean_inc(x_888);
lean_inc(x_887);
lean_dec(x_789);
x_889 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_889, 0, x_887);
lean_ctor_set(x_889, 1, x_888);
return x_889;
}
}
}
else
{
uint8_t x_890; 
lean_dec(x_783);
lean_dec(x_778);
lean_dec(x_771);
lean_dec(x_5);
lean_dec(x_2);
x_890 = !lean_is_exclusive(x_784);
if (x_890 == 0)
{
return x_784;
}
else
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; 
x_891 = lean_ctor_get(x_784, 0);
x_892 = lean_ctor_get(x_784, 1);
lean_inc(x_892);
lean_inc(x_891);
lean_dec(x_784);
x_893 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_893, 0, x_891);
lean_ctor_set(x_893, 1, x_892);
return x_893;
}
}
}
else
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; 
lean_dec(x_771);
lean_dec(x_5);
x_894 = lean_ctor_get(x_781, 0);
lean_inc(x_894);
lean_dec(x_781);
x_895 = lean_box(0);
x_896 = l_Lean_mkConst(x_894, x_895);
lean_inc(x_2);
lean_inc(x_896);
x_897 = l_Lean_Meta_inferType(x_896, x_2, x_758);
if (lean_obj_tag(x_897) == 0)
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; 
x_898 = lean_ctor_get(x_897, 0);
lean_inc(x_898);
x_899 = lean_ctor_get(x_897, 1);
lean_inc(x_899);
lean_dec(x_897);
x_900 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__19___boxed), 6, 2);
lean_closure_set(x_900, 0, x_778);
lean_closure_set(x_900, 1, x_896);
x_901 = l_Lean_Meta_forallTelescope___rarg(x_898, x_900, x_2, x_899);
return x_901;
}
else
{
uint8_t x_902; 
lean_dec(x_896);
lean_dec(x_778);
lean_dec(x_2);
x_902 = !lean_is_exclusive(x_897);
if (x_902 == 0)
{
return x_897;
}
else
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; 
x_903 = lean_ctor_get(x_897, 0);
x_904 = lean_ctor_get(x_897, 1);
lean_inc(x_904);
lean_inc(x_903);
lean_dec(x_897);
x_905 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_905, 0, x_903);
lean_ctor_set(x_905, 1, x_904);
return x_905;
}
}
}
}
else
{
lean_object* x_906; 
lean_dec(x_759);
x_906 = lean_box(0);
x_760 = x_906;
goto block_770;
}
block_770:
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_dec(x_760);
x_761 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_762 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_762, 0, x_761);
x_763 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_763, 0, x_762);
x_764 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_765 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_765, 0, x_764);
lean_ctor_set(x_765, 1, x_763);
x_766 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_767 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_767, 0, x_765);
lean_ctor_set(x_767, 1, x_766);
x_768 = lean_box(0);
x_769 = l_Lean_Meta_throwOther___rarg(x_767, x_768, x_2, x_758);
lean_dec(x_2);
return x_769;
}
}
case 8:
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; 
x_907 = lean_ctor_get(x_4, 1);
lean_inc(x_907);
lean_dec(x_4);
x_908 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_908) == 4)
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; 
x_920 = lean_ctor_get(x_908, 0);
lean_inc(x_920);
lean_dec(x_908);
x_921 = lean_unsigned_to_nat(0u);
x_922 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_921);
x_923 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_922);
x_924 = lean_mk_array(x_922, x_923);
x_925 = lean_unsigned_to_nat(1u);
x_926 = lean_nat_sub(x_922, x_925);
lean_dec(x_922);
lean_inc(x_5);
x_927 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_924, x_926);
x_928 = lean_ctor_get(x_907, 0);
lean_inc(x_928);
x_929 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_930 = l_Lean_CombinatorCompilerAttribute_getDeclFor(x_929, x_928, x_920);
lean_dec(x_928);
if (lean_obj_tag(x_930) == 0)
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; 
x_931 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
x_932 = l_Lean_Name_append___main(x_920, x_931);
lean_inc(x_920);
x_933 = l_Lean_Meta_getConstInfo(x_920, x_2, x_907);
if (lean_obj_tag(x_933) == 0)
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
x_934 = lean_ctor_get(x_933, 0);
lean_inc(x_934);
x_935 = lean_ctor_get(x_933, 1);
lean_inc(x_935);
lean_dec(x_933);
x_936 = l_Lean_ConstantInfo_type(x_934);
x_937 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_936);
x_938 = l_Lean_Meta_forallTelescope___rarg(x_936, x_937, x_2, x_935);
if (lean_obj_tag(x_938) == 0)
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_1010; uint8_t x_1011; 
x_939 = lean_ctor_get(x_938, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_938, 1);
lean_inc(x_940);
lean_dec(x_938);
x_1010 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8;
x_1011 = l_Lean_Expr_isConstOf(x_939, x_1010);
if (x_1011 == 0)
{
lean_object* x_1012; uint8_t x_1013; 
x_1012 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_1013 = l_Lean_Expr_isConstOf(x_939, x_1012);
lean_dec(x_939);
if (x_1013 == 0)
{
lean_object* x_1014; 
lean_dec(x_936);
lean_dec(x_934);
lean_dec(x_932);
lean_dec(x_927);
lean_dec(x_920);
lean_inc(x_2);
lean_inc(x_5);
x_1014 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_940);
if (lean_obj_tag(x_1014) == 0)
{
lean_object* x_1015; 
x_1015 = lean_ctor_get(x_1014, 0);
lean_inc(x_1015);
if (lean_obj_tag(x_1015) == 0)
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
x_1016 = lean_ctor_get(x_1014, 1);
lean_inc(x_1016);
lean_dec(x_1014);
x_1017 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1018 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1018, 0, x_1017);
x_1019 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1019, 0, x_1018);
x_1020 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__11;
x_1021 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1021, 0, x_1020);
lean_ctor_set(x_1021, 1, x_1019);
x_1022 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_1023 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1023, 0, x_1021);
lean_ctor_set(x_1023, 1, x_1022);
x_1024 = lean_box(0);
x_1025 = l_Lean_Meta_throwOther___rarg(x_1023, x_1024, x_2, x_1016);
lean_dec(x_2);
return x_1025;
}
else
{
lean_object* x_1026; lean_object* x_1027; 
lean_dec(x_5);
x_1026 = lean_ctor_get(x_1014, 1);
lean_inc(x_1026);
lean_dec(x_1014);
x_1027 = lean_ctor_get(x_1015, 0);
lean_inc(x_1027);
lean_dec(x_1015);
x_1 = x_1027;
x_3 = x_1026;
goto _start;
}
}
else
{
uint8_t x_1029; 
lean_dec(x_5);
lean_dec(x_2);
x_1029 = !lean_is_exclusive(x_1014);
if (x_1029 == 0)
{
return x_1014;
}
else
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
x_1030 = lean_ctor_get(x_1014, 0);
x_1031 = lean_ctor_get(x_1014, 1);
lean_inc(x_1031);
lean_inc(x_1030);
lean_dec(x_1014);
x_1032 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1032, 0, x_1030);
lean_ctor_set(x_1032, 1, x_1031);
return x_1032;
}
}
}
else
{
lean_object* x_1033; 
x_1033 = lean_box(0);
x_941 = x_1033;
goto block_1009;
}
}
else
{
lean_object* x_1034; 
lean_dec(x_939);
x_1034 = lean_box(0);
x_941 = x_1034;
goto block_1009;
}
block_1009:
{
lean_object* x_942; 
lean_dec(x_941);
x_942 = l_Lean_ConstantInfo_value_x3f(x_934);
lean_dec(x_934);
if (lean_obj_tag(x_942) == 0)
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; 
lean_dec(x_936);
lean_dec(x_932);
lean_dec(x_927);
lean_dec(x_920);
x_943 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_944 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_944, 0, x_943);
x_945 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_945, 0, x_944);
x_946 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_947 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_947, 0, x_946);
lean_ctor_set(x_947, 1, x_945);
x_948 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_949 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_949, 0, x_947);
lean_ctor_set(x_949, 1, x_948);
x_950 = lean_box(0);
x_951 = l_Lean_Meta_throwOther___rarg(x_949, x_950, x_2, x_940);
lean_dec(x_2);
return x_951;
}
else
{
lean_object* x_952; lean_object* x_953; lean_object* x_954; 
lean_dec(x_5);
x_952 = lean_ctor_get(x_942, 0);
lean_inc(x_952);
lean_dec(x_942);
x_953 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_952);
lean_inc(x_2);
x_954 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_953, x_2, x_940);
if (lean_obj_tag(x_954) == 0)
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_975; lean_object* x_976; 
x_955 = lean_ctor_get(x_954, 0);
lean_inc(x_955);
x_956 = lean_ctor_get(x_954, 1);
lean_inc(x_956);
lean_dec(x_954);
x_975 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__18;
lean_inc(x_2);
x_976 = l_Lean_Meta_forallTelescope___rarg(x_936, x_975, x_2, x_956);
if (lean_obj_tag(x_976) == 0)
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; uint8_t x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; 
x_977 = lean_ctor_get(x_976, 0);
lean_inc(x_977);
x_978 = lean_ctor_get(x_976, 1);
lean_inc(x_978);
lean_dec(x_976);
x_979 = lean_box(0);
lean_inc(x_932);
x_980 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_980, 0, x_932);
lean_ctor_set(x_980, 1, x_979);
lean_ctor_set(x_980, 2, x_977);
x_981 = lean_box(0);
x_982 = 0;
x_983 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_983, 0, x_980);
lean_ctor_set(x_983, 1, x_955);
lean_ctor_set(x_983, 2, x_981);
lean_ctor_set_uint8(x_983, sizeof(void*)*3, x_982);
x_984 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_984, 0, x_983);
x_985 = lean_ctor_get(x_978, 0);
lean_inc(x_985);
x_986 = l_Lean_Options_empty;
x_987 = l_Lean_Environment_addAndCompile(x_985, x_986, x_984);
lean_dec(x_984);
if (lean_obj_tag(x_987) == 0)
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; uint8_t x_996; 
lean_dec(x_932);
lean_dec(x_927);
lean_dec(x_920);
x_988 = lean_ctor_get(x_987, 0);
lean_inc(x_988);
lean_dec(x_987);
x_989 = l_Lean_KernelException_toMessageData(x_988, x_986);
x_990 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_989);
x_991 = l_Lean_Format_pretty(x_990, x_986);
x_992 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_992, 0, x_991);
x_993 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_993, 0, x_992);
x_994 = lean_box(0);
x_995 = l_Lean_Meta_throwOther___rarg(x_993, x_994, x_2, x_978);
lean_dec(x_2);
x_996 = !lean_is_exclusive(x_995);
if (x_996 == 0)
{
return x_995;
}
else
{
lean_object* x_997; lean_object* x_998; lean_object* x_999; 
x_997 = lean_ctor_get(x_995, 0);
x_998 = lean_ctor_get(x_995, 1);
lean_inc(x_998);
lean_inc(x_997);
lean_dec(x_995);
x_999 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_999, 0, x_997);
lean_ctor_set(x_999, 1, x_998);
return x_999;
}
}
else
{
lean_object* x_1000; 
x_1000 = lean_ctor_get(x_987, 0);
lean_inc(x_1000);
lean_dec(x_987);
x_957 = x_1000;
x_958 = x_978;
goto block_974;
}
}
else
{
uint8_t x_1001; 
lean_dec(x_955);
lean_dec(x_932);
lean_dec(x_927);
lean_dec(x_920);
lean_dec(x_2);
x_1001 = !lean_is_exclusive(x_976);
if (x_1001 == 0)
{
return x_976;
}
else
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; 
x_1002 = lean_ctor_get(x_976, 0);
x_1003 = lean_ctor_get(x_976, 1);
lean_inc(x_1003);
lean_inc(x_1002);
lean_dec(x_976);
x_1004 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1004, 0, x_1002);
lean_ctor_set(x_1004, 1, x_1003);
return x_1004;
}
}
block_974:
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; 
lean_inc(x_932);
x_959 = l_Lean_CombinatorCompilerAttribute_setDeclFor(x_929, x_957, x_920, x_932);
x_960 = l_Lean_Meta_setEnv(x_959, x_2, x_958);
x_961 = lean_ctor_get(x_960, 1);
lean_inc(x_961);
lean_dec(x_960);
x_962 = lean_box(0);
x_963 = l_Lean_mkConst(x_932, x_962);
lean_inc(x_2);
lean_inc(x_963);
x_964 = l_Lean_Meta_inferType(x_963, x_2, x_961);
if (lean_obj_tag(x_964) == 0)
{
lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; 
x_965 = lean_ctor_get(x_964, 0);
lean_inc(x_965);
x_966 = lean_ctor_get(x_964, 1);
lean_inc(x_966);
lean_dec(x_964);
x_967 = l_Lean_mkAppStx___closed__2;
x_968 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__20___boxed), 8, 4);
lean_closure_set(x_968, 0, x_937);
lean_closure_set(x_968, 1, x_967);
lean_closure_set(x_968, 2, x_927);
lean_closure_set(x_968, 3, x_963);
x_969 = l_Lean_Meta_forallTelescope___rarg(x_965, x_968, x_2, x_966);
return x_969;
}
else
{
uint8_t x_970; 
lean_dec(x_963);
lean_dec(x_927);
lean_dec(x_2);
x_970 = !lean_is_exclusive(x_964);
if (x_970 == 0)
{
return x_964;
}
else
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; 
x_971 = lean_ctor_get(x_964, 0);
x_972 = lean_ctor_get(x_964, 1);
lean_inc(x_972);
lean_inc(x_971);
lean_dec(x_964);
x_973 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_973, 0, x_971);
lean_ctor_set(x_973, 1, x_972);
return x_973;
}
}
}
}
else
{
uint8_t x_1005; 
lean_dec(x_936);
lean_dec(x_932);
lean_dec(x_927);
lean_dec(x_920);
lean_dec(x_2);
x_1005 = !lean_is_exclusive(x_954);
if (x_1005 == 0)
{
return x_954;
}
else
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; 
x_1006 = lean_ctor_get(x_954, 0);
x_1007 = lean_ctor_get(x_954, 1);
lean_inc(x_1007);
lean_inc(x_1006);
lean_dec(x_954);
x_1008 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1008, 0, x_1006);
lean_ctor_set(x_1008, 1, x_1007);
return x_1008;
}
}
}
}
}
else
{
uint8_t x_1035; 
lean_dec(x_936);
lean_dec(x_934);
lean_dec(x_932);
lean_dec(x_927);
lean_dec(x_920);
lean_dec(x_5);
lean_dec(x_2);
x_1035 = !lean_is_exclusive(x_938);
if (x_1035 == 0)
{
return x_938;
}
else
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
x_1036 = lean_ctor_get(x_938, 0);
x_1037 = lean_ctor_get(x_938, 1);
lean_inc(x_1037);
lean_inc(x_1036);
lean_dec(x_938);
x_1038 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1038, 0, x_1036);
lean_ctor_set(x_1038, 1, x_1037);
return x_1038;
}
}
}
else
{
uint8_t x_1039; 
lean_dec(x_932);
lean_dec(x_927);
lean_dec(x_920);
lean_dec(x_5);
lean_dec(x_2);
x_1039 = !lean_is_exclusive(x_933);
if (x_1039 == 0)
{
return x_933;
}
else
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; 
x_1040 = lean_ctor_get(x_933, 0);
x_1041 = lean_ctor_get(x_933, 1);
lean_inc(x_1041);
lean_inc(x_1040);
lean_dec(x_933);
x_1042 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1042, 0, x_1040);
lean_ctor_set(x_1042, 1, x_1041);
return x_1042;
}
}
}
else
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; 
lean_dec(x_920);
lean_dec(x_5);
x_1043 = lean_ctor_get(x_930, 0);
lean_inc(x_1043);
lean_dec(x_930);
x_1044 = lean_box(0);
x_1045 = l_Lean_mkConst(x_1043, x_1044);
lean_inc(x_2);
lean_inc(x_1045);
x_1046 = l_Lean_Meta_inferType(x_1045, x_2, x_907);
if (lean_obj_tag(x_1046) == 0)
{
lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; 
x_1047 = lean_ctor_get(x_1046, 0);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_1046, 1);
lean_inc(x_1048);
lean_dec(x_1046);
x_1049 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__22___boxed), 6, 2);
lean_closure_set(x_1049, 0, x_927);
lean_closure_set(x_1049, 1, x_1045);
x_1050 = l_Lean_Meta_forallTelescope___rarg(x_1047, x_1049, x_2, x_1048);
return x_1050;
}
else
{
uint8_t x_1051; 
lean_dec(x_1045);
lean_dec(x_927);
lean_dec(x_2);
x_1051 = !lean_is_exclusive(x_1046);
if (x_1051 == 0)
{
return x_1046;
}
else
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
x_1052 = lean_ctor_get(x_1046, 0);
x_1053 = lean_ctor_get(x_1046, 1);
lean_inc(x_1053);
lean_inc(x_1052);
lean_dec(x_1046);
x_1054 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1054, 0, x_1052);
lean_ctor_set(x_1054, 1, x_1053);
return x_1054;
}
}
}
}
else
{
lean_object* x_1055; 
lean_dec(x_908);
x_1055 = lean_box(0);
x_909 = x_1055;
goto block_919;
}
block_919:
{
lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; 
lean_dec(x_909);
x_910 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_911 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_911, 0, x_910);
x_912 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_912, 0, x_911);
x_913 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_914 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_914, 0, x_913);
lean_ctor_set(x_914, 1, x_912);
x_915 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_916 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_916, 0, x_914);
lean_ctor_set(x_916, 1, x_915);
x_917 = lean_box(0);
x_918 = l_Lean_Meta_throwOther___rarg(x_916, x_917, x_2, x_907);
lean_dec(x_2);
return x_918;
}
}
case 9:
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; 
x_1056 = lean_ctor_get(x_4, 1);
lean_inc(x_1056);
lean_dec(x_4);
x_1057 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_1057) == 4)
{
lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
x_1069 = lean_ctor_get(x_1057, 0);
lean_inc(x_1069);
lean_dec(x_1057);
x_1070 = lean_unsigned_to_nat(0u);
x_1071 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_1070);
x_1072 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1071);
x_1073 = lean_mk_array(x_1071, x_1072);
x_1074 = lean_unsigned_to_nat(1u);
x_1075 = lean_nat_sub(x_1071, x_1074);
lean_dec(x_1071);
lean_inc(x_5);
x_1076 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_1073, x_1075);
x_1077 = lean_ctor_get(x_1056, 0);
lean_inc(x_1077);
x_1078 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_1079 = l_Lean_CombinatorCompilerAttribute_getDeclFor(x_1078, x_1077, x_1069);
lean_dec(x_1077);
if (lean_obj_tag(x_1079) == 0)
{
lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; 
x_1080 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
x_1081 = l_Lean_Name_append___main(x_1069, x_1080);
lean_inc(x_1069);
x_1082 = l_Lean_Meta_getConstInfo(x_1069, x_2, x_1056);
if (lean_obj_tag(x_1082) == 0)
{
lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
x_1083 = lean_ctor_get(x_1082, 0);
lean_inc(x_1083);
x_1084 = lean_ctor_get(x_1082, 1);
lean_inc(x_1084);
lean_dec(x_1082);
x_1085 = l_Lean_ConstantInfo_type(x_1083);
x_1086 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_1085);
x_1087 = l_Lean_Meta_forallTelescope___rarg(x_1085, x_1086, x_2, x_1084);
if (lean_obj_tag(x_1087) == 0)
{
lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1159; uint8_t x_1160; 
x_1088 = lean_ctor_get(x_1087, 0);
lean_inc(x_1088);
x_1089 = lean_ctor_get(x_1087, 1);
lean_inc(x_1089);
lean_dec(x_1087);
x_1159 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8;
x_1160 = l_Lean_Expr_isConstOf(x_1088, x_1159);
if (x_1160 == 0)
{
lean_object* x_1161; uint8_t x_1162; 
x_1161 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_1162 = l_Lean_Expr_isConstOf(x_1088, x_1161);
lean_dec(x_1088);
if (x_1162 == 0)
{
lean_object* x_1163; 
lean_dec(x_1085);
lean_dec(x_1083);
lean_dec(x_1081);
lean_dec(x_1076);
lean_dec(x_1069);
lean_inc(x_2);
lean_inc(x_5);
x_1163 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_1089);
if (lean_obj_tag(x_1163) == 0)
{
lean_object* x_1164; 
x_1164 = lean_ctor_get(x_1163, 0);
lean_inc(x_1164);
if (lean_obj_tag(x_1164) == 0)
{
lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; 
x_1165 = lean_ctor_get(x_1163, 1);
lean_inc(x_1165);
lean_dec(x_1163);
x_1166 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1167 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1167, 0, x_1166);
x_1168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1168, 0, x_1167);
x_1169 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__11;
x_1170 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1170, 0, x_1169);
lean_ctor_set(x_1170, 1, x_1168);
x_1171 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_1172 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1172, 0, x_1170);
lean_ctor_set(x_1172, 1, x_1171);
x_1173 = lean_box(0);
x_1174 = l_Lean_Meta_throwOther___rarg(x_1172, x_1173, x_2, x_1165);
lean_dec(x_2);
return x_1174;
}
else
{
lean_object* x_1175; lean_object* x_1176; 
lean_dec(x_5);
x_1175 = lean_ctor_get(x_1163, 1);
lean_inc(x_1175);
lean_dec(x_1163);
x_1176 = lean_ctor_get(x_1164, 0);
lean_inc(x_1176);
lean_dec(x_1164);
x_1 = x_1176;
x_3 = x_1175;
goto _start;
}
}
else
{
uint8_t x_1178; 
lean_dec(x_5);
lean_dec(x_2);
x_1178 = !lean_is_exclusive(x_1163);
if (x_1178 == 0)
{
return x_1163;
}
else
{
lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; 
x_1179 = lean_ctor_get(x_1163, 0);
x_1180 = lean_ctor_get(x_1163, 1);
lean_inc(x_1180);
lean_inc(x_1179);
lean_dec(x_1163);
x_1181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1181, 0, x_1179);
lean_ctor_set(x_1181, 1, x_1180);
return x_1181;
}
}
}
else
{
lean_object* x_1182; 
x_1182 = lean_box(0);
x_1090 = x_1182;
goto block_1158;
}
}
else
{
lean_object* x_1183; 
lean_dec(x_1088);
x_1183 = lean_box(0);
x_1090 = x_1183;
goto block_1158;
}
block_1158:
{
lean_object* x_1091; 
lean_dec(x_1090);
x_1091 = l_Lean_ConstantInfo_value_x3f(x_1083);
lean_dec(x_1083);
if (lean_obj_tag(x_1091) == 0)
{
lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; 
lean_dec(x_1085);
lean_dec(x_1081);
lean_dec(x_1076);
lean_dec(x_1069);
x_1092 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1093 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1093, 0, x_1092);
x_1094 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1094, 0, x_1093);
x_1095 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_1096 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1096, 0, x_1095);
lean_ctor_set(x_1096, 1, x_1094);
x_1097 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_1098 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1098, 0, x_1096);
lean_ctor_set(x_1098, 1, x_1097);
x_1099 = lean_box(0);
x_1100 = l_Lean_Meta_throwOther___rarg(x_1098, x_1099, x_2, x_1089);
lean_dec(x_2);
return x_1100;
}
else
{
lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; 
lean_dec(x_5);
x_1101 = lean_ctor_get(x_1091, 0);
lean_inc(x_1101);
lean_dec(x_1091);
x_1102 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_1101);
lean_inc(x_2);
x_1103 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_1102, x_2, x_1089);
if (lean_obj_tag(x_1103) == 0)
{
lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1124; lean_object* x_1125; 
x_1104 = lean_ctor_get(x_1103, 0);
lean_inc(x_1104);
x_1105 = lean_ctor_get(x_1103, 1);
lean_inc(x_1105);
lean_dec(x_1103);
x_1124 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__19;
lean_inc(x_2);
x_1125 = l_Lean_Meta_forallTelescope___rarg(x_1085, x_1124, x_2, x_1105);
if (lean_obj_tag(x_1125) == 0)
{
lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; uint8_t x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; 
x_1126 = lean_ctor_get(x_1125, 0);
lean_inc(x_1126);
x_1127 = lean_ctor_get(x_1125, 1);
lean_inc(x_1127);
lean_dec(x_1125);
x_1128 = lean_box(0);
lean_inc(x_1081);
x_1129 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1129, 0, x_1081);
lean_ctor_set(x_1129, 1, x_1128);
lean_ctor_set(x_1129, 2, x_1126);
x_1130 = lean_box(0);
x_1131 = 0;
x_1132 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1132, 0, x_1129);
lean_ctor_set(x_1132, 1, x_1104);
lean_ctor_set(x_1132, 2, x_1130);
lean_ctor_set_uint8(x_1132, sizeof(void*)*3, x_1131);
x_1133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1133, 0, x_1132);
x_1134 = lean_ctor_get(x_1127, 0);
lean_inc(x_1134);
x_1135 = l_Lean_Options_empty;
x_1136 = l_Lean_Environment_addAndCompile(x_1134, x_1135, x_1133);
lean_dec(x_1133);
if (lean_obj_tag(x_1136) == 0)
{
lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; uint8_t x_1145; 
lean_dec(x_1081);
lean_dec(x_1076);
lean_dec(x_1069);
x_1137 = lean_ctor_get(x_1136, 0);
lean_inc(x_1137);
lean_dec(x_1136);
x_1138 = l_Lean_KernelException_toMessageData(x_1137, x_1135);
x_1139 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1138);
x_1140 = l_Lean_Format_pretty(x_1139, x_1135);
x_1141 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1141, 0, x_1140);
x_1142 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1142, 0, x_1141);
x_1143 = lean_box(0);
x_1144 = l_Lean_Meta_throwOther___rarg(x_1142, x_1143, x_2, x_1127);
lean_dec(x_2);
x_1145 = !lean_is_exclusive(x_1144);
if (x_1145 == 0)
{
return x_1144;
}
else
{
lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; 
x_1146 = lean_ctor_get(x_1144, 0);
x_1147 = lean_ctor_get(x_1144, 1);
lean_inc(x_1147);
lean_inc(x_1146);
lean_dec(x_1144);
x_1148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1148, 0, x_1146);
lean_ctor_set(x_1148, 1, x_1147);
return x_1148;
}
}
else
{
lean_object* x_1149; 
x_1149 = lean_ctor_get(x_1136, 0);
lean_inc(x_1149);
lean_dec(x_1136);
x_1106 = x_1149;
x_1107 = x_1127;
goto block_1123;
}
}
else
{
uint8_t x_1150; 
lean_dec(x_1104);
lean_dec(x_1081);
lean_dec(x_1076);
lean_dec(x_1069);
lean_dec(x_2);
x_1150 = !lean_is_exclusive(x_1125);
if (x_1150 == 0)
{
return x_1125;
}
else
{
lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; 
x_1151 = lean_ctor_get(x_1125, 0);
x_1152 = lean_ctor_get(x_1125, 1);
lean_inc(x_1152);
lean_inc(x_1151);
lean_dec(x_1125);
x_1153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1153, 0, x_1151);
lean_ctor_set(x_1153, 1, x_1152);
return x_1153;
}
}
block_1123:
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; 
lean_inc(x_1081);
x_1108 = l_Lean_CombinatorCompilerAttribute_setDeclFor(x_1078, x_1106, x_1069, x_1081);
x_1109 = l_Lean_Meta_setEnv(x_1108, x_2, x_1107);
x_1110 = lean_ctor_get(x_1109, 1);
lean_inc(x_1110);
lean_dec(x_1109);
x_1111 = lean_box(0);
x_1112 = l_Lean_mkConst(x_1081, x_1111);
lean_inc(x_2);
lean_inc(x_1112);
x_1113 = l_Lean_Meta_inferType(x_1112, x_2, x_1110);
if (lean_obj_tag(x_1113) == 0)
{
lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
x_1114 = lean_ctor_get(x_1113, 0);
lean_inc(x_1114);
x_1115 = lean_ctor_get(x_1113, 1);
lean_inc(x_1115);
lean_dec(x_1113);
x_1116 = l_Lean_mkAppStx___closed__2;
x_1117 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__23___boxed), 8, 4);
lean_closure_set(x_1117, 0, x_1086);
lean_closure_set(x_1117, 1, x_1116);
lean_closure_set(x_1117, 2, x_1076);
lean_closure_set(x_1117, 3, x_1112);
x_1118 = l_Lean_Meta_forallTelescope___rarg(x_1114, x_1117, x_2, x_1115);
return x_1118;
}
else
{
uint8_t x_1119; 
lean_dec(x_1112);
lean_dec(x_1076);
lean_dec(x_2);
x_1119 = !lean_is_exclusive(x_1113);
if (x_1119 == 0)
{
return x_1113;
}
else
{
lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; 
x_1120 = lean_ctor_get(x_1113, 0);
x_1121 = lean_ctor_get(x_1113, 1);
lean_inc(x_1121);
lean_inc(x_1120);
lean_dec(x_1113);
x_1122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1122, 0, x_1120);
lean_ctor_set(x_1122, 1, x_1121);
return x_1122;
}
}
}
}
else
{
uint8_t x_1154; 
lean_dec(x_1085);
lean_dec(x_1081);
lean_dec(x_1076);
lean_dec(x_1069);
lean_dec(x_2);
x_1154 = !lean_is_exclusive(x_1103);
if (x_1154 == 0)
{
return x_1103;
}
else
{
lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; 
x_1155 = lean_ctor_get(x_1103, 0);
x_1156 = lean_ctor_get(x_1103, 1);
lean_inc(x_1156);
lean_inc(x_1155);
lean_dec(x_1103);
x_1157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1157, 0, x_1155);
lean_ctor_set(x_1157, 1, x_1156);
return x_1157;
}
}
}
}
}
else
{
uint8_t x_1184; 
lean_dec(x_1085);
lean_dec(x_1083);
lean_dec(x_1081);
lean_dec(x_1076);
lean_dec(x_1069);
lean_dec(x_5);
lean_dec(x_2);
x_1184 = !lean_is_exclusive(x_1087);
if (x_1184 == 0)
{
return x_1087;
}
else
{
lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; 
x_1185 = lean_ctor_get(x_1087, 0);
x_1186 = lean_ctor_get(x_1087, 1);
lean_inc(x_1186);
lean_inc(x_1185);
lean_dec(x_1087);
x_1187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1187, 0, x_1185);
lean_ctor_set(x_1187, 1, x_1186);
return x_1187;
}
}
}
else
{
uint8_t x_1188; 
lean_dec(x_1081);
lean_dec(x_1076);
lean_dec(x_1069);
lean_dec(x_5);
lean_dec(x_2);
x_1188 = !lean_is_exclusive(x_1082);
if (x_1188 == 0)
{
return x_1082;
}
else
{
lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; 
x_1189 = lean_ctor_get(x_1082, 0);
x_1190 = lean_ctor_get(x_1082, 1);
lean_inc(x_1190);
lean_inc(x_1189);
lean_dec(x_1082);
x_1191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1191, 0, x_1189);
lean_ctor_set(x_1191, 1, x_1190);
return x_1191;
}
}
}
else
{
lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; 
lean_dec(x_1069);
lean_dec(x_5);
x_1192 = lean_ctor_get(x_1079, 0);
lean_inc(x_1192);
lean_dec(x_1079);
x_1193 = lean_box(0);
x_1194 = l_Lean_mkConst(x_1192, x_1193);
lean_inc(x_2);
lean_inc(x_1194);
x_1195 = l_Lean_Meta_inferType(x_1194, x_2, x_1056);
if (lean_obj_tag(x_1195) == 0)
{
lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; 
x_1196 = lean_ctor_get(x_1195, 0);
lean_inc(x_1196);
x_1197 = lean_ctor_get(x_1195, 1);
lean_inc(x_1197);
lean_dec(x_1195);
x_1198 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__25___boxed), 6, 2);
lean_closure_set(x_1198, 0, x_1076);
lean_closure_set(x_1198, 1, x_1194);
x_1199 = l_Lean_Meta_forallTelescope___rarg(x_1196, x_1198, x_2, x_1197);
return x_1199;
}
else
{
uint8_t x_1200; 
lean_dec(x_1194);
lean_dec(x_1076);
lean_dec(x_2);
x_1200 = !lean_is_exclusive(x_1195);
if (x_1200 == 0)
{
return x_1195;
}
else
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; 
x_1201 = lean_ctor_get(x_1195, 0);
x_1202 = lean_ctor_get(x_1195, 1);
lean_inc(x_1202);
lean_inc(x_1201);
lean_dec(x_1195);
x_1203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1203, 0, x_1201);
lean_ctor_set(x_1203, 1, x_1202);
return x_1203;
}
}
}
}
else
{
lean_object* x_1204; 
lean_dec(x_1057);
x_1204 = lean_box(0);
x_1058 = x_1204;
goto block_1068;
}
block_1068:
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; 
lean_dec(x_1058);
x_1059 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1060 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1060, 0, x_1059);
x_1061 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1061, 0, x_1060);
x_1062 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_1063 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1063, 0, x_1062);
lean_ctor_set(x_1063, 1, x_1061);
x_1064 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_1065 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1065, 0, x_1063);
lean_ctor_set(x_1065, 1, x_1064);
x_1066 = lean_box(0);
x_1067 = l_Lean_Meta_throwOther___rarg(x_1065, x_1066, x_2, x_1056);
lean_dec(x_2);
return x_1067;
}
}
case 10:
{
lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; 
x_1205 = lean_ctor_get(x_4, 1);
lean_inc(x_1205);
lean_dec(x_4);
x_1206 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_1206) == 4)
{
lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; 
x_1218 = lean_ctor_get(x_1206, 0);
lean_inc(x_1218);
lean_dec(x_1206);
x_1219 = lean_unsigned_to_nat(0u);
x_1220 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_1219);
x_1221 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1220);
x_1222 = lean_mk_array(x_1220, x_1221);
x_1223 = lean_unsigned_to_nat(1u);
x_1224 = lean_nat_sub(x_1220, x_1223);
lean_dec(x_1220);
lean_inc(x_5);
x_1225 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_1222, x_1224);
x_1226 = lean_ctor_get(x_1205, 0);
lean_inc(x_1226);
x_1227 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_1228 = l_Lean_CombinatorCompilerAttribute_getDeclFor(x_1227, x_1226, x_1218);
lean_dec(x_1226);
if (lean_obj_tag(x_1228) == 0)
{
lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; 
x_1229 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
x_1230 = l_Lean_Name_append___main(x_1218, x_1229);
lean_inc(x_1218);
x_1231 = l_Lean_Meta_getConstInfo(x_1218, x_2, x_1205);
if (lean_obj_tag(x_1231) == 0)
{
lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; 
x_1232 = lean_ctor_get(x_1231, 0);
lean_inc(x_1232);
x_1233 = lean_ctor_get(x_1231, 1);
lean_inc(x_1233);
lean_dec(x_1231);
x_1234 = l_Lean_ConstantInfo_type(x_1232);
x_1235 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_1234);
x_1236 = l_Lean_Meta_forallTelescope___rarg(x_1234, x_1235, x_2, x_1233);
if (lean_obj_tag(x_1236) == 0)
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1308; uint8_t x_1309; 
x_1237 = lean_ctor_get(x_1236, 0);
lean_inc(x_1237);
x_1238 = lean_ctor_get(x_1236, 1);
lean_inc(x_1238);
lean_dec(x_1236);
x_1308 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8;
x_1309 = l_Lean_Expr_isConstOf(x_1237, x_1308);
if (x_1309 == 0)
{
lean_object* x_1310; uint8_t x_1311; 
x_1310 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_1311 = l_Lean_Expr_isConstOf(x_1237, x_1310);
lean_dec(x_1237);
if (x_1311 == 0)
{
lean_object* x_1312; 
lean_dec(x_1234);
lean_dec(x_1232);
lean_dec(x_1230);
lean_dec(x_1225);
lean_dec(x_1218);
lean_inc(x_2);
lean_inc(x_5);
x_1312 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_1238);
if (lean_obj_tag(x_1312) == 0)
{
lean_object* x_1313; 
x_1313 = lean_ctor_get(x_1312, 0);
lean_inc(x_1313);
if (lean_obj_tag(x_1313) == 0)
{
lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; 
x_1314 = lean_ctor_get(x_1312, 1);
lean_inc(x_1314);
lean_dec(x_1312);
x_1315 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1316 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1316, 0, x_1315);
x_1317 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1317, 0, x_1316);
x_1318 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__11;
x_1319 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1319, 0, x_1318);
lean_ctor_set(x_1319, 1, x_1317);
x_1320 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_1321 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1321, 0, x_1319);
lean_ctor_set(x_1321, 1, x_1320);
x_1322 = lean_box(0);
x_1323 = l_Lean_Meta_throwOther___rarg(x_1321, x_1322, x_2, x_1314);
lean_dec(x_2);
return x_1323;
}
else
{
lean_object* x_1324; lean_object* x_1325; 
lean_dec(x_5);
x_1324 = lean_ctor_get(x_1312, 1);
lean_inc(x_1324);
lean_dec(x_1312);
x_1325 = lean_ctor_get(x_1313, 0);
lean_inc(x_1325);
lean_dec(x_1313);
x_1 = x_1325;
x_3 = x_1324;
goto _start;
}
}
else
{
uint8_t x_1327; 
lean_dec(x_5);
lean_dec(x_2);
x_1327 = !lean_is_exclusive(x_1312);
if (x_1327 == 0)
{
return x_1312;
}
else
{
lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; 
x_1328 = lean_ctor_get(x_1312, 0);
x_1329 = lean_ctor_get(x_1312, 1);
lean_inc(x_1329);
lean_inc(x_1328);
lean_dec(x_1312);
x_1330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1330, 0, x_1328);
lean_ctor_set(x_1330, 1, x_1329);
return x_1330;
}
}
}
else
{
lean_object* x_1331; 
x_1331 = lean_box(0);
x_1239 = x_1331;
goto block_1307;
}
}
else
{
lean_object* x_1332; 
lean_dec(x_1237);
x_1332 = lean_box(0);
x_1239 = x_1332;
goto block_1307;
}
block_1307:
{
lean_object* x_1240; 
lean_dec(x_1239);
x_1240 = l_Lean_ConstantInfo_value_x3f(x_1232);
lean_dec(x_1232);
if (lean_obj_tag(x_1240) == 0)
{
lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; 
lean_dec(x_1234);
lean_dec(x_1230);
lean_dec(x_1225);
lean_dec(x_1218);
x_1241 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1242 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1242, 0, x_1241);
x_1243 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1243, 0, x_1242);
x_1244 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_1245 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1245, 0, x_1244);
lean_ctor_set(x_1245, 1, x_1243);
x_1246 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_1247 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1247, 0, x_1245);
lean_ctor_set(x_1247, 1, x_1246);
x_1248 = lean_box(0);
x_1249 = l_Lean_Meta_throwOther___rarg(x_1247, x_1248, x_2, x_1238);
lean_dec(x_2);
return x_1249;
}
else
{
lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; 
lean_dec(x_5);
x_1250 = lean_ctor_get(x_1240, 0);
lean_inc(x_1250);
lean_dec(x_1240);
x_1251 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_1250);
lean_inc(x_2);
x_1252 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_1251, x_2, x_1238);
if (lean_obj_tag(x_1252) == 0)
{
lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1273; lean_object* x_1274; 
x_1253 = lean_ctor_get(x_1252, 0);
lean_inc(x_1253);
x_1254 = lean_ctor_get(x_1252, 1);
lean_inc(x_1254);
lean_dec(x_1252);
x_1273 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__20;
lean_inc(x_2);
x_1274 = l_Lean_Meta_forallTelescope___rarg(x_1234, x_1273, x_2, x_1254);
if (lean_obj_tag(x_1274) == 0)
{
lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; uint8_t x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; 
x_1275 = lean_ctor_get(x_1274, 0);
lean_inc(x_1275);
x_1276 = lean_ctor_get(x_1274, 1);
lean_inc(x_1276);
lean_dec(x_1274);
x_1277 = lean_box(0);
lean_inc(x_1230);
x_1278 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1278, 0, x_1230);
lean_ctor_set(x_1278, 1, x_1277);
lean_ctor_set(x_1278, 2, x_1275);
x_1279 = lean_box(0);
x_1280 = 0;
x_1281 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1281, 0, x_1278);
lean_ctor_set(x_1281, 1, x_1253);
lean_ctor_set(x_1281, 2, x_1279);
lean_ctor_set_uint8(x_1281, sizeof(void*)*3, x_1280);
x_1282 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1282, 0, x_1281);
x_1283 = lean_ctor_get(x_1276, 0);
lean_inc(x_1283);
x_1284 = l_Lean_Options_empty;
x_1285 = l_Lean_Environment_addAndCompile(x_1283, x_1284, x_1282);
lean_dec(x_1282);
if (lean_obj_tag(x_1285) == 0)
{
lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; uint8_t x_1294; 
lean_dec(x_1230);
lean_dec(x_1225);
lean_dec(x_1218);
x_1286 = lean_ctor_get(x_1285, 0);
lean_inc(x_1286);
lean_dec(x_1285);
x_1287 = l_Lean_KernelException_toMessageData(x_1286, x_1284);
x_1288 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1287);
x_1289 = l_Lean_Format_pretty(x_1288, x_1284);
x_1290 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1290, 0, x_1289);
x_1291 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1291, 0, x_1290);
x_1292 = lean_box(0);
x_1293 = l_Lean_Meta_throwOther___rarg(x_1291, x_1292, x_2, x_1276);
lean_dec(x_2);
x_1294 = !lean_is_exclusive(x_1293);
if (x_1294 == 0)
{
return x_1293;
}
else
{
lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; 
x_1295 = lean_ctor_get(x_1293, 0);
x_1296 = lean_ctor_get(x_1293, 1);
lean_inc(x_1296);
lean_inc(x_1295);
lean_dec(x_1293);
x_1297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1297, 0, x_1295);
lean_ctor_set(x_1297, 1, x_1296);
return x_1297;
}
}
else
{
lean_object* x_1298; 
x_1298 = lean_ctor_get(x_1285, 0);
lean_inc(x_1298);
lean_dec(x_1285);
x_1255 = x_1298;
x_1256 = x_1276;
goto block_1272;
}
}
else
{
uint8_t x_1299; 
lean_dec(x_1253);
lean_dec(x_1230);
lean_dec(x_1225);
lean_dec(x_1218);
lean_dec(x_2);
x_1299 = !lean_is_exclusive(x_1274);
if (x_1299 == 0)
{
return x_1274;
}
else
{
lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; 
x_1300 = lean_ctor_get(x_1274, 0);
x_1301 = lean_ctor_get(x_1274, 1);
lean_inc(x_1301);
lean_inc(x_1300);
lean_dec(x_1274);
x_1302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1302, 0, x_1300);
lean_ctor_set(x_1302, 1, x_1301);
return x_1302;
}
}
block_1272:
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; 
lean_inc(x_1230);
x_1257 = l_Lean_CombinatorCompilerAttribute_setDeclFor(x_1227, x_1255, x_1218, x_1230);
x_1258 = l_Lean_Meta_setEnv(x_1257, x_2, x_1256);
x_1259 = lean_ctor_get(x_1258, 1);
lean_inc(x_1259);
lean_dec(x_1258);
x_1260 = lean_box(0);
x_1261 = l_Lean_mkConst(x_1230, x_1260);
lean_inc(x_2);
lean_inc(x_1261);
x_1262 = l_Lean_Meta_inferType(x_1261, x_2, x_1259);
if (lean_obj_tag(x_1262) == 0)
{
lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; 
x_1263 = lean_ctor_get(x_1262, 0);
lean_inc(x_1263);
x_1264 = lean_ctor_get(x_1262, 1);
lean_inc(x_1264);
lean_dec(x_1262);
x_1265 = l_Lean_mkAppStx___closed__2;
x_1266 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__26___boxed), 8, 4);
lean_closure_set(x_1266, 0, x_1235);
lean_closure_set(x_1266, 1, x_1265);
lean_closure_set(x_1266, 2, x_1225);
lean_closure_set(x_1266, 3, x_1261);
x_1267 = l_Lean_Meta_forallTelescope___rarg(x_1263, x_1266, x_2, x_1264);
return x_1267;
}
else
{
uint8_t x_1268; 
lean_dec(x_1261);
lean_dec(x_1225);
lean_dec(x_2);
x_1268 = !lean_is_exclusive(x_1262);
if (x_1268 == 0)
{
return x_1262;
}
else
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; 
x_1269 = lean_ctor_get(x_1262, 0);
x_1270 = lean_ctor_get(x_1262, 1);
lean_inc(x_1270);
lean_inc(x_1269);
lean_dec(x_1262);
x_1271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1271, 0, x_1269);
lean_ctor_set(x_1271, 1, x_1270);
return x_1271;
}
}
}
}
else
{
uint8_t x_1303; 
lean_dec(x_1234);
lean_dec(x_1230);
lean_dec(x_1225);
lean_dec(x_1218);
lean_dec(x_2);
x_1303 = !lean_is_exclusive(x_1252);
if (x_1303 == 0)
{
return x_1252;
}
else
{
lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; 
x_1304 = lean_ctor_get(x_1252, 0);
x_1305 = lean_ctor_get(x_1252, 1);
lean_inc(x_1305);
lean_inc(x_1304);
lean_dec(x_1252);
x_1306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1306, 0, x_1304);
lean_ctor_set(x_1306, 1, x_1305);
return x_1306;
}
}
}
}
}
else
{
uint8_t x_1333; 
lean_dec(x_1234);
lean_dec(x_1232);
lean_dec(x_1230);
lean_dec(x_1225);
lean_dec(x_1218);
lean_dec(x_5);
lean_dec(x_2);
x_1333 = !lean_is_exclusive(x_1236);
if (x_1333 == 0)
{
return x_1236;
}
else
{
lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; 
x_1334 = lean_ctor_get(x_1236, 0);
x_1335 = lean_ctor_get(x_1236, 1);
lean_inc(x_1335);
lean_inc(x_1334);
lean_dec(x_1236);
x_1336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1336, 0, x_1334);
lean_ctor_set(x_1336, 1, x_1335);
return x_1336;
}
}
}
else
{
uint8_t x_1337; 
lean_dec(x_1230);
lean_dec(x_1225);
lean_dec(x_1218);
lean_dec(x_5);
lean_dec(x_2);
x_1337 = !lean_is_exclusive(x_1231);
if (x_1337 == 0)
{
return x_1231;
}
else
{
lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; 
x_1338 = lean_ctor_get(x_1231, 0);
x_1339 = lean_ctor_get(x_1231, 1);
lean_inc(x_1339);
lean_inc(x_1338);
lean_dec(x_1231);
x_1340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1340, 0, x_1338);
lean_ctor_set(x_1340, 1, x_1339);
return x_1340;
}
}
}
else
{
lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; 
lean_dec(x_1218);
lean_dec(x_5);
x_1341 = lean_ctor_get(x_1228, 0);
lean_inc(x_1341);
lean_dec(x_1228);
x_1342 = lean_box(0);
x_1343 = l_Lean_mkConst(x_1341, x_1342);
lean_inc(x_2);
lean_inc(x_1343);
x_1344 = l_Lean_Meta_inferType(x_1343, x_2, x_1205);
if (lean_obj_tag(x_1344) == 0)
{
lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; 
x_1345 = lean_ctor_get(x_1344, 0);
lean_inc(x_1345);
x_1346 = lean_ctor_get(x_1344, 1);
lean_inc(x_1346);
lean_dec(x_1344);
x_1347 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__28___boxed), 6, 2);
lean_closure_set(x_1347, 0, x_1225);
lean_closure_set(x_1347, 1, x_1343);
x_1348 = l_Lean_Meta_forallTelescope___rarg(x_1345, x_1347, x_2, x_1346);
return x_1348;
}
else
{
uint8_t x_1349; 
lean_dec(x_1343);
lean_dec(x_1225);
lean_dec(x_2);
x_1349 = !lean_is_exclusive(x_1344);
if (x_1349 == 0)
{
return x_1344;
}
else
{
lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; 
x_1350 = lean_ctor_get(x_1344, 0);
x_1351 = lean_ctor_get(x_1344, 1);
lean_inc(x_1351);
lean_inc(x_1350);
lean_dec(x_1344);
x_1352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1352, 0, x_1350);
lean_ctor_set(x_1352, 1, x_1351);
return x_1352;
}
}
}
}
else
{
lean_object* x_1353; 
lean_dec(x_1206);
x_1353 = lean_box(0);
x_1207 = x_1353;
goto block_1217;
}
block_1217:
{
lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; 
lean_dec(x_1207);
x_1208 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1209 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1209, 0, x_1208);
x_1210 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1210, 0, x_1209);
x_1211 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_1212 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1212, 0, x_1211);
lean_ctor_set(x_1212, 1, x_1210);
x_1213 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_1214 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1214, 0, x_1212);
lean_ctor_set(x_1214, 1, x_1213);
x_1215 = lean_box(0);
x_1216 = l_Lean_Meta_throwOther___rarg(x_1214, x_1215, x_2, x_1205);
lean_dec(x_2);
return x_1216;
}
}
case 11:
{
lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; 
x_1354 = lean_ctor_get(x_4, 1);
lean_inc(x_1354);
lean_dec(x_4);
x_1355 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_1355) == 4)
{
lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; 
x_1367 = lean_ctor_get(x_1355, 0);
lean_inc(x_1367);
lean_dec(x_1355);
x_1368 = lean_unsigned_to_nat(0u);
x_1369 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_1368);
x_1370 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1369);
x_1371 = lean_mk_array(x_1369, x_1370);
x_1372 = lean_unsigned_to_nat(1u);
x_1373 = lean_nat_sub(x_1369, x_1372);
lean_dec(x_1369);
lean_inc(x_5);
x_1374 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_1371, x_1373);
x_1375 = lean_ctor_get(x_1354, 0);
lean_inc(x_1375);
x_1376 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_1377 = l_Lean_CombinatorCompilerAttribute_getDeclFor(x_1376, x_1375, x_1367);
lean_dec(x_1375);
if (lean_obj_tag(x_1377) == 0)
{
lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; 
x_1378 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
x_1379 = l_Lean_Name_append___main(x_1367, x_1378);
lean_inc(x_1367);
x_1380 = l_Lean_Meta_getConstInfo(x_1367, x_2, x_1354);
if (lean_obj_tag(x_1380) == 0)
{
lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; 
x_1381 = lean_ctor_get(x_1380, 0);
lean_inc(x_1381);
x_1382 = lean_ctor_get(x_1380, 1);
lean_inc(x_1382);
lean_dec(x_1380);
x_1383 = l_Lean_ConstantInfo_type(x_1381);
x_1384 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_1383);
x_1385 = l_Lean_Meta_forallTelescope___rarg(x_1383, x_1384, x_2, x_1382);
if (lean_obj_tag(x_1385) == 0)
{
lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1457; uint8_t x_1458; 
x_1386 = lean_ctor_get(x_1385, 0);
lean_inc(x_1386);
x_1387 = lean_ctor_get(x_1385, 1);
lean_inc(x_1387);
lean_dec(x_1385);
x_1457 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8;
x_1458 = l_Lean_Expr_isConstOf(x_1386, x_1457);
if (x_1458 == 0)
{
lean_object* x_1459; uint8_t x_1460; 
x_1459 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_1460 = l_Lean_Expr_isConstOf(x_1386, x_1459);
lean_dec(x_1386);
if (x_1460 == 0)
{
lean_object* x_1461; 
lean_dec(x_1383);
lean_dec(x_1381);
lean_dec(x_1379);
lean_dec(x_1374);
lean_dec(x_1367);
lean_inc(x_2);
lean_inc(x_5);
x_1461 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_1387);
if (lean_obj_tag(x_1461) == 0)
{
lean_object* x_1462; 
x_1462 = lean_ctor_get(x_1461, 0);
lean_inc(x_1462);
if (lean_obj_tag(x_1462) == 0)
{
lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; 
x_1463 = lean_ctor_get(x_1461, 1);
lean_inc(x_1463);
lean_dec(x_1461);
x_1464 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1465 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1465, 0, x_1464);
x_1466 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1466, 0, x_1465);
x_1467 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__11;
x_1468 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1468, 0, x_1467);
lean_ctor_set(x_1468, 1, x_1466);
x_1469 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_1470 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1470, 0, x_1468);
lean_ctor_set(x_1470, 1, x_1469);
x_1471 = lean_box(0);
x_1472 = l_Lean_Meta_throwOther___rarg(x_1470, x_1471, x_2, x_1463);
lean_dec(x_2);
return x_1472;
}
else
{
lean_object* x_1473; lean_object* x_1474; 
lean_dec(x_5);
x_1473 = lean_ctor_get(x_1461, 1);
lean_inc(x_1473);
lean_dec(x_1461);
x_1474 = lean_ctor_get(x_1462, 0);
lean_inc(x_1474);
lean_dec(x_1462);
x_1 = x_1474;
x_3 = x_1473;
goto _start;
}
}
else
{
uint8_t x_1476; 
lean_dec(x_5);
lean_dec(x_2);
x_1476 = !lean_is_exclusive(x_1461);
if (x_1476 == 0)
{
return x_1461;
}
else
{
lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; 
x_1477 = lean_ctor_get(x_1461, 0);
x_1478 = lean_ctor_get(x_1461, 1);
lean_inc(x_1478);
lean_inc(x_1477);
lean_dec(x_1461);
x_1479 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1479, 0, x_1477);
lean_ctor_set(x_1479, 1, x_1478);
return x_1479;
}
}
}
else
{
lean_object* x_1480; 
x_1480 = lean_box(0);
x_1388 = x_1480;
goto block_1456;
}
}
else
{
lean_object* x_1481; 
lean_dec(x_1386);
x_1481 = lean_box(0);
x_1388 = x_1481;
goto block_1456;
}
block_1456:
{
lean_object* x_1389; 
lean_dec(x_1388);
x_1389 = l_Lean_ConstantInfo_value_x3f(x_1381);
lean_dec(x_1381);
if (lean_obj_tag(x_1389) == 0)
{
lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; 
lean_dec(x_1383);
lean_dec(x_1379);
lean_dec(x_1374);
lean_dec(x_1367);
x_1390 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1391 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1391, 0, x_1390);
x_1392 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1392, 0, x_1391);
x_1393 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_1394 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1394, 0, x_1393);
lean_ctor_set(x_1394, 1, x_1392);
x_1395 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_1396 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1396, 0, x_1394);
lean_ctor_set(x_1396, 1, x_1395);
x_1397 = lean_box(0);
x_1398 = l_Lean_Meta_throwOther___rarg(x_1396, x_1397, x_2, x_1387);
lean_dec(x_2);
return x_1398;
}
else
{
lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; 
lean_dec(x_5);
x_1399 = lean_ctor_get(x_1389, 0);
lean_inc(x_1399);
lean_dec(x_1389);
x_1400 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_1399);
lean_inc(x_2);
x_1401 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_1400, x_2, x_1387);
if (lean_obj_tag(x_1401) == 0)
{
lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1422; lean_object* x_1423; 
x_1402 = lean_ctor_get(x_1401, 0);
lean_inc(x_1402);
x_1403 = lean_ctor_get(x_1401, 1);
lean_inc(x_1403);
lean_dec(x_1401);
x_1422 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__21;
lean_inc(x_2);
x_1423 = l_Lean_Meta_forallTelescope___rarg(x_1383, x_1422, x_2, x_1403);
if (lean_obj_tag(x_1423) == 0)
{
lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; uint8_t x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; 
x_1424 = lean_ctor_get(x_1423, 0);
lean_inc(x_1424);
x_1425 = lean_ctor_get(x_1423, 1);
lean_inc(x_1425);
lean_dec(x_1423);
x_1426 = lean_box(0);
lean_inc(x_1379);
x_1427 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1427, 0, x_1379);
lean_ctor_set(x_1427, 1, x_1426);
lean_ctor_set(x_1427, 2, x_1424);
x_1428 = lean_box(0);
x_1429 = 0;
x_1430 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1430, 0, x_1427);
lean_ctor_set(x_1430, 1, x_1402);
lean_ctor_set(x_1430, 2, x_1428);
lean_ctor_set_uint8(x_1430, sizeof(void*)*3, x_1429);
x_1431 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1431, 0, x_1430);
x_1432 = lean_ctor_get(x_1425, 0);
lean_inc(x_1432);
x_1433 = l_Lean_Options_empty;
x_1434 = l_Lean_Environment_addAndCompile(x_1432, x_1433, x_1431);
lean_dec(x_1431);
if (lean_obj_tag(x_1434) == 0)
{
lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; uint8_t x_1443; 
lean_dec(x_1379);
lean_dec(x_1374);
lean_dec(x_1367);
x_1435 = lean_ctor_get(x_1434, 0);
lean_inc(x_1435);
lean_dec(x_1434);
x_1436 = l_Lean_KernelException_toMessageData(x_1435, x_1433);
x_1437 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1436);
x_1438 = l_Lean_Format_pretty(x_1437, x_1433);
x_1439 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1439, 0, x_1438);
x_1440 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1440, 0, x_1439);
x_1441 = lean_box(0);
x_1442 = l_Lean_Meta_throwOther___rarg(x_1440, x_1441, x_2, x_1425);
lean_dec(x_2);
x_1443 = !lean_is_exclusive(x_1442);
if (x_1443 == 0)
{
return x_1442;
}
else
{
lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; 
x_1444 = lean_ctor_get(x_1442, 0);
x_1445 = lean_ctor_get(x_1442, 1);
lean_inc(x_1445);
lean_inc(x_1444);
lean_dec(x_1442);
x_1446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1446, 0, x_1444);
lean_ctor_set(x_1446, 1, x_1445);
return x_1446;
}
}
else
{
lean_object* x_1447; 
x_1447 = lean_ctor_get(x_1434, 0);
lean_inc(x_1447);
lean_dec(x_1434);
x_1404 = x_1447;
x_1405 = x_1425;
goto block_1421;
}
}
else
{
uint8_t x_1448; 
lean_dec(x_1402);
lean_dec(x_1379);
lean_dec(x_1374);
lean_dec(x_1367);
lean_dec(x_2);
x_1448 = !lean_is_exclusive(x_1423);
if (x_1448 == 0)
{
return x_1423;
}
else
{
lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; 
x_1449 = lean_ctor_get(x_1423, 0);
x_1450 = lean_ctor_get(x_1423, 1);
lean_inc(x_1450);
lean_inc(x_1449);
lean_dec(x_1423);
x_1451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1451, 0, x_1449);
lean_ctor_set(x_1451, 1, x_1450);
return x_1451;
}
}
block_1421:
{
lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; 
lean_inc(x_1379);
x_1406 = l_Lean_CombinatorCompilerAttribute_setDeclFor(x_1376, x_1404, x_1367, x_1379);
x_1407 = l_Lean_Meta_setEnv(x_1406, x_2, x_1405);
x_1408 = lean_ctor_get(x_1407, 1);
lean_inc(x_1408);
lean_dec(x_1407);
x_1409 = lean_box(0);
x_1410 = l_Lean_mkConst(x_1379, x_1409);
lean_inc(x_2);
lean_inc(x_1410);
x_1411 = l_Lean_Meta_inferType(x_1410, x_2, x_1408);
if (lean_obj_tag(x_1411) == 0)
{
lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; 
x_1412 = lean_ctor_get(x_1411, 0);
lean_inc(x_1412);
x_1413 = lean_ctor_get(x_1411, 1);
lean_inc(x_1413);
lean_dec(x_1411);
x_1414 = l_Lean_mkAppStx___closed__2;
x_1415 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__29___boxed), 8, 4);
lean_closure_set(x_1415, 0, x_1384);
lean_closure_set(x_1415, 1, x_1414);
lean_closure_set(x_1415, 2, x_1374);
lean_closure_set(x_1415, 3, x_1410);
x_1416 = l_Lean_Meta_forallTelescope___rarg(x_1412, x_1415, x_2, x_1413);
return x_1416;
}
else
{
uint8_t x_1417; 
lean_dec(x_1410);
lean_dec(x_1374);
lean_dec(x_2);
x_1417 = !lean_is_exclusive(x_1411);
if (x_1417 == 0)
{
return x_1411;
}
else
{
lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; 
x_1418 = lean_ctor_get(x_1411, 0);
x_1419 = lean_ctor_get(x_1411, 1);
lean_inc(x_1419);
lean_inc(x_1418);
lean_dec(x_1411);
x_1420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1420, 0, x_1418);
lean_ctor_set(x_1420, 1, x_1419);
return x_1420;
}
}
}
}
else
{
uint8_t x_1452; 
lean_dec(x_1383);
lean_dec(x_1379);
lean_dec(x_1374);
lean_dec(x_1367);
lean_dec(x_2);
x_1452 = !lean_is_exclusive(x_1401);
if (x_1452 == 0)
{
return x_1401;
}
else
{
lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; 
x_1453 = lean_ctor_get(x_1401, 0);
x_1454 = lean_ctor_get(x_1401, 1);
lean_inc(x_1454);
lean_inc(x_1453);
lean_dec(x_1401);
x_1455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1455, 0, x_1453);
lean_ctor_set(x_1455, 1, x_1454);
return x_1455;
}
}
}
}
}
else
{
uint8_t x_1482; 
lean_dec(x_1383);
lean_dec(x_1381);
lean_dec(x_1379);
lean_dec(x_1374);
lean_dec(x_1367);
lean_dec(x_5);
lean_dec(x_2);
x_1482 = !lean_is_exclusive(x_1385);
if (x_1482 == 0)
{
return x_1385;
}
else
{
lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; 
x_1483 = lean_ctor_get(x_1385, 0);
x_1484 = lean_ctor_get(x_1385, 1);
lean_inc(x_1484);
lean_inc(x_1483);
lean_dec(x_1385);
x_1485 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1485, 0, x_1483);
lean_ctor_set(x_1485, 1, x_1484);
return x_1485;
}
}
}
else
{
uint8_t x_1486; 
lean_dec(x_1379);
lean_dec(x_1374);
lean_dec(x_1367);
lean_dec(x_5);
lean_dec(x_2);
x_1486 = !lean_is_exclusive(x_1380);
if (x_1486 == 0)
{
return x_1380;
}
else
{
lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; 
x_1487 = lean_ctor_get(x_1380, 0);
x_1488 = lean_ctor_get(x_1380, 1);
lean_inc(x_1488);
lean_inc(x_1487);
lean_dec(x_1380);
x_1489 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1489, 0, x_1487);
lean_ctor_set(x_1489, 1, x_1488);
return x_1489;
}
}
}
else
{
lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; 
lean_dec(x_1367);
lean_dec(x_5);
x_1490 = lean_ctor_get(x_1377, 0);
lean_inc(x_1490);
lean_dec(x_1377);
x_1491 = lean_box(0);
x_1492 = l_Lean_mkConst(x_1490, x_1491);
lean_inc(x_2);
lean_inc(x_1492);
x_1493 = l_Lean_Meta_inferType(x_1492, x_2, x_1354);
if (lean_obj_tag(x_1493) == 0)
{
lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; 
x_1494 = lean_ctor_get(x_1493, 0);
lean_inc(x_1494);
x_1495 = lean_ctor_get(x_1493, 1);
lean_inc(x_1495);
lean_dec(x_1493);
x_1496 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__31___boxed), 6, 2);
lean_closure_set(x_1496, 0, x_1374);
lean_closure_set(x_1496, 1, x_1492);
x_1497 = l_Lean_Meta_forallTelescope___rarg(x_1494, x_1496, x_2, x_1495);
return x_1497;
}
else
{
uint8_t x_1498; 
lean_dec(x_1492);
lean_dec(x_1374);
lean_dec(x_2);
x_1498 = !lean_is_exclusive(x_1493);
if (x_1498 == 0)
{
return x_1493;
}
else
{
lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; 
x_1499 = lean_ctor_get(x_1493, 0);
x_1500 = lean_ctor_get(x_1493, 1);
lean_inc(x_1500);
lean_inc(x_1499);
lean_dec(x_1493);
x_1501 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1501, 0, x_1499);
lean_ctor_set(x_1501, 1, x_1500);
return x_1501;
}
}
}
}
else
{
lean_object* x_1502; 
lean_dec(x_1355);
x_1502 = lean_box(0);
x_1356 = x_1502;
goto block_1366;
}
block_1366:
{
lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; 
lean_dec(x_1356);
x_1357 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1358 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1358, 0, x_1357);
x_1359 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1359, 0, x_1358);
x_1360 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_1361 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1361, 0, x_1360);
lean_ctor_set(x_1361, 1, x_1359);
x_1362 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_1363 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1363, 0, x_1361);
lean_ctor_set(x_1363, 1, x_1362);
x_1364 = lean_box(0);
x_1365 = l_Lean_Meta_throwOther___rarg(x_1363, x_1364, x_2, x_1354);
lean_dec(x_2);
return x_1365;
}
}
default: 
{
lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; 
x_1503 = lean_ctor_get(x_4, 1);
lean_inc(x_1503);
lean_dec(x_4);
x_1504 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_1504) == 4)
{
lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; 
x_1516 = lean_ctor_get(x_1504, 0);
lean_inc(x_1516);
lean_dec(x_1504);
x_1517 = lean_unsigned_to_nat(0u);
x_1518 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_1517);
x_1519 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1518);
x_1520 = lean_mk_array(x_1518, x_1519);
x_1521 = lean_unsigned_to_nat(1u);
x_1522 = lean_nat_sub(x_1518, x_1521);
lean_dec(x_1518);
lean_inc(x_5);
x_1523 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_1520, x_1522);
x_1524 = lean_ctor_get(x_1503, 0);
lean_inc(x_1524);
x_1525 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_1526 = l_Lean_CombinatorCompilerAttribute_getDeclFor(x_1525, x_1524, x_1516);
lean_dec(x_1524);
if (lean_obj_tag(x_1526) == 0)
{
lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; 
x_1527 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
x_1528 = l_Lean_Name_append___main(x_1516, x_1527);
lean_inc(x_1516);
x_1529 = l_Lean_Meta_getConstInfo(x_1516, x_2, x_1503);
if (lean_obj_tag(x_1529) == 0)
{
lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; 
x_1530 = lean_ctor_get(x_1529, 0);
lean_inc(x_1530);
x_1531 = lean_ctor_get(x_1529, 1);
lean_inc(x_1531);
lean_dec(x_1529);
x_1532 = l_Lean_ConstantInfo_type(x_1530);
x_1533 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_1532);
x_1534 = l_Lean_Meta_forallTelescope___rarg(x_1532, x_1533, x_2, x_1531);
if (lean_obj_tag(x_1534) == 0)
{
lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1606; uint8_t x_1607; 
x_1535 = lean_ctor_get(x_1534, 0);
lean_inc(x_1535);
x_1536 = lean_ctor_get(x_1534, 1);
lean_inc(x_1536);
lean_dec(x_1534);
x_1606 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8;
x_1607 = l_Lean_Expr_isConstOf(x_1535, x_1606);
if (x_1607 == 0)
{
lean_object* x_1608; uint8_t x_1609; 
x_1608 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_1609 = l_Lean_Expr_isConstOf(x_1535, x_1608);
lean_dec(x_1535);
if (x_1609 == 0)
{
lean_object* x_1610; 
lean_dec(x_1532);
lean_dec(x_1530);
lean_dec(x_1528);
lean_dec(x_1523);
lean_dec(x_1516);
lean_inc(x_2);
lean_inc(x_5);
x_1610 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_1536);
if (lean_obj_tag(x_1610) == 0)
{
lean_object* x_1611; 
x_1611 = lean_ctor_get(x_1610, 0);
lean_inc(x_1611);
if (lean_obj_tag(x_1611) == 0)
{
lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; 
x_1612 = lean_ctor_get(x_1610, 1);
lean_inc(x_1612);
lean_dec(x_1610);
x_1613 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1614 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1614, 0, x_1613);
x_1615 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1615, 0, x_1614);
x_1616 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__11;
x_1617 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1617, 0, x_1616);
lean_ctor_set(x_1617, 1, x_1615);
x_1618 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_1619 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1619, 0, x_1617);
lean_ctor_set(x_1619, 1, x_1618);
x_1620 = lean_box(0);
x_1621 = l_Lean_Meta_throwOther___rarg(x_1619, x_1620, x_2, x_1612);
lean_dec(x_2);
return x_1621;
}
else
{
lean_object* x_1622; lean_object* x_1623; 
lean_dec(x_5);
x_1622 = lean_ctor_get(x_1610, 1);
lean_inc(x_1622);
lean_dec(x_1610);
x_1623 = lean_ctor_get(x_1611, 0);
lean_inc(x_1623);
lean_dec(x_1611);
x_1 = x_1623;
x_3 = x_1622;
goto _start;
}
}
else
{
uint8_t x_1625; 
lean_dec(x_5);
lean_dec(x_2);
x_1625 = !lean_is_exclusive(x_1610);
if (x_1625 == 0)
{
return x_1610;
}
else
{
lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; 
x_1626 = lean_ctor_get(x_1610, 0);
x_1627 = lean_ctor_get(x_1610, 1);
lean_inc(x_1627);
lean_inc(x_1626);
lean_dec(x_1610);
x_1628 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1628, 0, x_1626);
lean_ctor_set(x_1628, 1, x_1627);
return x_1628;
}
}
}
else
{
lean_object* x_1629; 
x_1629 = lean_box(0);
x_1537 = x_1629;
goto block_1605;
}
}
else
{
lean_object* x_1630; 
lean_dec(x_1535);
x_1630 = lean_box(0);
x_1537 = x_1630;
goto block_1605;
}
block_1605:
{
lean_object* x_1538; 
lean_dec(x_1537);
x_1538 = l_Lean_ConstantInfo_value_x3f(x_1530);
lean_dec(x_1530);
if (lean_obj_tag(x_1538) == 0)
{
lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; 
lean_dec(x_1532);
lean_dec(x_1528);
lean_dec(x_1523);
lean_dec(x_1516);
x_1539 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1540 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1540, 0, x_1539);
x_1541 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1541, 0, x_1540);
x_1542 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_1543 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1543, 0, x_1542);
lean_ctor_set(x_1543, 1, x_1541);
x_1544 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_1545 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1545, 0, x_1543);
lean_ctor_set(x_1545, 1, x_1544);
x_1546 = lean_box(0);
x_1547 = l_Lean_Meta_throwOther___rarg(x_1545, x_1546, x_2, x_1536);
lean_dec(x_2);
return x_1547;
}
else
{
lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; 
lean_dec(x_5);
x_1548 = lean_ctor_get(x_1538, 0);
lean_inc(x_1548);
lean_dec(x_1538);
x_1549 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_1548);
lean_inc(x_2);
x_1550 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_1549, x_2, x_1536);
if (lean_obj_tag(x_1550) == 0)
{
lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1571; lean_object* x_1572; 
x_1551 = lean_ctor_get(x_1550, 0);
lean_inc(x_1551);
x_1552 = lean_ctor_get(x_1550, 1);
lean_inc(x_1552);
lean_dec(x_1550);
x_1571 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__22;
lean_inc(x_2);
x_1572 = l_Lean_Meta_forallTelescope___rarg(x_1532, x_1571, x_2, x_1552);
if (lean_obj_tag(x_1572) == 0)
{
lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; uint8_t x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; 
x_1573 = lean_ctor_get(x_1572, 0);
lean_inc(x_1573);
x_1574 = lean_ctor_get(x_1572, 1);
lean_inc(x_1574);
lean_dec(x_1572);
x_1575 = lean_box(0);
lean_inc(x_1528);
x_1576 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1576, 0, x_1528);
lean_ctor_set(x_1576, 1, x_1575);
lean_ctor_set(x_1576, 2, x_1573);
x_1577 = lean_box(0);
x_1578 = 0;
x_1579 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1579, 0, x_1576);
lean_ctor_set(x_1579, 1, x_1551);
lean_ctor_set(x_1579, 2, x_1577);
lean_ctor_set_uint8(x_1579, sizeof(void*)*3, x_1578);
x_1580 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1580, 0, x_1579);
x_1581 = lean_ctor_get(x_1574, 0);
lean_inc(x_1581);
x_1582 = l_Lean_Options_empty;
x_1583 = l_Lean_Environment_addAndCompile(x_1581, x_1582, x_1580);
lean_dec(x_1580);
if (lean_obj_tag(x_1583) == 0)
{
lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; uint8_t x_1592; 
lean_dec(x_1528);
lean_dec(x_1523);
lean_dec(x_1516);
x_1584 = lean_ctor_get(x_1583, 0);
lean_inc(x_1584);
lean_dec(x_1583);
x_1585 = l_Lean_KernelException_toMessageData(x_1584, x_1582);
x_1586 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1585);
x_1587 = l_Lean_Format_pretty(x_1586, x_1582);
x_1588 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1588, 0, x_1587);
x_1589 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1589, 0, x_1588);
x_1590 = lean_box(0);
x_1591 = l_Lean_Meta_throwOther___rarg(x_1589, x_1590, x_2, x_1574);
lean_dec(x_2);
x_1592 = !lean_is_exclusive(x_1591);
if (x_1592 == 0)
{
return x_1591;
}
else
{
lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; 
x_1593 = lean_ctor_get(x_1591, 0);
x_1594 = lean_ctor_get(x_1591, 1);
lean_inc(x_1594);
lean_inc(x_1593);
lean_dec(x_1591);
x_1595 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1595, 0, x_1593);
lean_ctor_set(x_1595, 1, x_1594);
return x_1595;
}
}
else
{
lean_object* x_1596; 
x_1596 = lean_ctor_get(x_1583, 0);
lean_inc(x_1596);
lean_dec(x_1583);
x_1553 = x_1596;
x_1554 = x_1574;
goto block_1570;
}
}
else
{
uint8_t x_1597; 
lean_dec(x_1551);
lean_dec(x_1528);
lean_dec(x_1523);
lean_dec(x_1516);
lean_dec(x_2);
x_1597 = !lean_is_exclusive(x_1572);
if (x_1597 == 0)
{
return x_1572;
}
else
{
lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; 
x_1598 = lean_ctor_get(x_1572, 0);
x_1599 = lean_ctor_get(x_1572, 1);
lean_inc(x_1599);
lean_inc(x_1598);
lean_dec(x_1572);
x_1600 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1600, 0, x_1598);
lean_ctor_set(x_1600, 1, x_1599);
return x_1600;
}
}
block_1570:
{
lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; 
lean_inc(x_1528);
x_1555 = l_Lean_CombinatorCompilerAttribute_setDeclFor(x_1525, x_1553, x_1516, x_1528);
x_1556 = l_Lean_Meta_setEnv(x_1555, x_2, x_1554);
x_1557 = lean_ctor_get(x_1556, 1);
lean_inc(x_1557);
lean_dec(x_1556);
x_1558 = lean_box(0);
x_1559 = l_Lean_mkConst(x_1528, x_1558);
lean_inc(x_2);
lean_inc(x_1559);
x_1560 = l_Lean_Meta_inferType(x_1559, x_2, x_1557);
if (lean_obj_tag(x_1560) == 0)
{
lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; 
x_1561 = lean_ctor_get(x_1560, 0);
lean_inc(x_1561);
x_1562 = lean_ctor_get(x_1560, 1);
lean_inc(x_1562);
lean_dec(x_1560);
x_1563 = l_Lean_mkAppStx___closed__2;
x_1564 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__32___boxed), 8, 4);
lean_closure_set(x_1564, 0, x_1533);
lean_closure_set(x_1564, 1, x_1563);
lean_closure_set(x_1564, 2, x_1523);
lean_closure_set(x_1564, 3, x_1559);
x_1565 = l_Lean_Meta_forallTelescope___rarg(x_1561, x_1564, x_2, x_1562);
return x_1565;
}
else
{
uint8_t x_1566; 
lean_dec(x_1559);
lean_dec(x_1523);
lean_dec(x_2);
x_1566 = !lean_is_exclusive(x_1560);
if (x_1566 == 0)
{
return x_1560;
}
else
{
lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; 
x_1567 = lean_ctor_get(x_1560, 0);
x_1568 = lean_ctor_get(x_1560, 1);
lean_inc(x_1568);
lean_inc(x_1567);
lean_dec(x_1560);
x_1569 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1569, 0, x_1567);
lean_ctor_set(x_1569, 1, x_1568);
return x_1569;
}
}
}
}
else
{
uint8_t x_1601; 
lean_dec(x_1532);
lean_dec(x_1528);
lean_dec(x_1523);
lean_dec(x_1516);
lean_dec(x_2);
x_1601 = !lean_is_exclusive(x_1550);
if (x_1601 == 0)
{
return x_1550;
}
else
{
lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; 
x_1602 = lean_ctor_get(x_1550, 0);
x_1603 = lean_ctor_get(x_1550, 1);
lean_inc(x_1603);
lean_inc(x_1602);
lean_dec(x_1550);
x_1604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1604, 0, x_1602);
lean_ctor_set(x_1604, 1, x_1603);
return x_1604;
}
}
}
}
}
else
{
uint8_t x_1631; 
lean_dec(x_1532);
lean_dec(x_1530);
lean_dec(x_1528);
lean_dec(x_1523);
lean_dec(x_1516);
lean_dec(x_5);
lean_dec(x_2);
x_1631 = !lean_is_exclusive(x_1534);
if (x_1631 == 0)
{
return x_1534;
}
else
{
lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; 
x_1632 = lean_ctor_get(x_1534, 0);
x_1633 = lean_ctor_get(x_1534, 1);
lean_inc(x_1633);
lean_inc(x_1632);
lean_dec(x_1534);
x_1634 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1634, 0, x_1632);
lean_ctor_set(x_1634, 1, x_1633);
return x_1634;
}
}
}
else
{
uint8_t x_1635; 
lean_dec(x_1528);
lean_dec(x_1523);
lean_dec(x_1516);
lean_dec(x_5);
lean_dec(x_2);
x_1635 = !lean_is_exclusive(x_1529);
if (x_1635 == 0)
{
return x_1529;
}
else
{
lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; 
x_1636 = lean_ctor_get(x_1529, 0);
x_1637 = lean_ctor_get(x_1529, 1);
lean_inc(x_1637);
lean_inc(x_1636);
lean_dec(x_1529);
x_1638 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1638, 0, x_1636);
lean_ctor_set(x_1638, 1, x_1637);
return x_1638;
}
}
}
else
{
lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; 
lean_dec(x_1516);
lean_dec(x_5);
x_1639 = lean_ctor_get(x_1526, 0);
lean_inc(x_1639);
lean_dec(x_1526);
x_1640 = lean_box(0);
x_1641 = l_Lean_mkConst(x_1639, x_1640);
lean_inc(x_2);
lean_inc(x_1641);
x_1642 = l_Lean_Meta_inferType(x_1641, x_2, x_1503);
if (lean_obj_tag(x_1642) == 0)
{
lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; 
x_1643 = lean_ctor_get(x_1642, 0);
lean_inc(x_1643);
x_1644 = lean_ctor_get(x_1642, 1);
lean_inc(x_1644);
lean_dec(x_1642);
x_1645 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__34___boxed), 6, 2);
lean_closure_set(x_1645, 0, x_1523);
lean_closure_set(x_1645, 1, x_1641);
x_1646 = l_Lean_Meta_forallTelescope___rarg(x_1643, x_1645, x_2, x_1644);
return x_1646;
}
else
{
uint8_t x_1647; 
lean_dec(x_1641);
lean_dec(x_1523);
lean_dec(x_2);
x_1647 = !lean_is_exclusive(x_1642);
if (x_1647 == 0)
{
return x_1642;
}
else
{
lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; 
x_1648 = lean_ctor_get(x_1642, 0);
x_1649 = lean_ctor_get(x_1642, 1);
lean_inc(x_1649);
lean_inc(x_1648);
lean_dec(x_1642);
x_1650 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1650, 0, x_1648);
lean_ctor_set(x_1650, 1, x_1649);
return x_1650;
}
}
}
}
else
{
lean_object* x_1651; 
lean_dec(x_1504);
x_1651 = lean_box(0);
x_1505 = x_1651;
goto block_1515;
}
block_1515:
{
lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; 
lean_dec(x_1505);
x_1506 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1507 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1507, 0, x_1506);
x_1508 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1508, 0, x_1507);
x_1509 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_1510 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1510, 0, x_1509);
lean_ctor_set(x_1510, 1, x_1508);
x_1511 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_1512 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1512, 0, x_1510);
lean_ctor_set(x_1512, 1, x_1511);
x_1513 = lean_box(0);
x_1514 = l_Lean_Meta_throwOther___rarg(x_1512, x_1513, x_2, x_1503);
lean_dec(x_2);
return x_1514;
}
}
}
}
else
{
uint8_t x_1652; 
lean_dec(x_2);
x_1652 = !lean_is_exclusive(x_4);
if (x_1652 == 0)
{
return x_4;
}
else
{
lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; 
x_1653 = lean_ctor_get(x_4, 0);
x_1654 = lean_ctor_get(x_4, 1);
lean_inc(x_1654);
lean_inc(x_1653);
lean_dec(x_4);
x_1655 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1655, 0, x_1653);
lean_ctor_set(x_1655, 1, x_1654);
return x_1655;
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__20(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__21(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__22(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__23(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__24(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__25(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__26(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__27(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__28(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__29(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__30(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__31(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__32(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__33(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__11(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__12(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__14(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__15(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__18(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__19(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__20(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__21(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__22(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__23(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__24(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__25(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__26(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__27(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__28(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__29(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__30(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__31(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__32(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__33(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__34(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParser___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_run___rarg___closed__1;
x_2 = l_Lean_LocalContext_Inhabited___closed__2;
x_3 = l_Array_empty___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_defaultMaxRecDepth;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParser___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_Error_Inhabited;
x_2 = lean_alloc_closure((void*)(l_EStateM_Inhabited___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParser(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_box(0);
lean_inc(x_2);
x_6 = l_Lean_mkConst(x_2, x_5);
x_7 = l_Lean_MetavarContext_Inhabited___closed__1;
x_8 = l_Lean_Meta_run___rarg___closed__5;
x_9 = l_Lean_NameGenerator_Inhabited___closed__3;
x_10 = l_Lean_TraceState_Inhabited___closed__1;
x_11 = l_Std_PersistentArray_empty___closed__3;
x_12 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_10);
lean_ctor_set(x_12, 5, x_11);
x_13 = l_Lean_PrettyPrinter_Parenthesizer_compileParser___closed__1;
x_14 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_6, x_13, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 4);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Std_PersistentArray_forM___at_IO_runMeta___spec__3(x_18, x_4);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
if (lean_obj_tag(x_15) == 4)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_mk_syntax_ident(x_2);
x_24 = l_Lean_mkOptionalNode___closed__2;
x_25 = lean_array_push(x_24, x_23);
x_26 = l_Lean_nullKind;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
if (x_3 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
x_29 = 1;
x_30 = lean_add_attribute(x_22, x_21, x_28, x_27, x_29, x_20);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__2;
x_32 = 1;
x_33 = lean_add_attribute(x_22, x_21, x_31, x_27, x_32, x_20);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_dec(x_19);
x_35 = l_Lean_PrettyPrinter_Parenthesizer_compileParser___closed__2;
x_36 = l_unreachable_x21___rarg(x_35);
x_37 = lean_apply_1(x_36, x_34);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
x_42 = lean_ctor_get(x_14, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_14, 1);
lean_inc(x_43);
lean_dec(x_14);
x_44 = lean_ctor_get(x_43, 4);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Std_PersistentArray_forM___at_IO_runMeta___spec__3(x_45, x_4);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = l_Lean_Meta_Exception_toStr(x_42);
x_50 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = l_Lean_Meta_Exception_toStr(x_42);
x_53 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_42);
x_55 = !lean_is_exclusive(x_46);
if (x_55 == 0)
{
return x_46;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_46, 0);
x_57 = lean_ctor_get(x_46, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_46);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParser___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_PrettyPrinter_Parenthesizer_compileParser(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_IO_ofExcept___at_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
lean_inc(x_3);
x_5 = lean_environment_find(x_3, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_1);
x_8 = l_Lean_Environment_evalConstCheck___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_15 = l_Lean_ConstantInfo_type(x_14);
lean_dec(x_14);
x_16 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8;
x_17 = l_Lean_Expr_isConstOf(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_19 = l_Lean_Expr_isConstOf(x_15, x_18);
lean_dec(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_eval_const(x_3, x_1);
lean_dec(x_1);
x_21 = l_IO_ofExcept___at_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___spec__1(x_20, x_4);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_apply_3(x_2, x_22, x_3, x_23);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
x_29 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_30 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_29, x_3, x_1);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; lean_object* x_32; 
x_31 = 0;
lean_inc(x_1);
x_32 = l_Lean_PrettyPrinter_Parenthesizer_compileParser(x_3, x_1, x_31, x_4);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind), 5, 1);
lean_closure_set(x_35, 0, x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind), 5, 1);
lean_closure_set(x_39, 0, x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_32);
if (x_42 == 0)
{
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_32);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_1);
x_46 = lean_ctor_get(x_30, 0);
lean_inc(x_46);
lean_dec(x_30);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_3);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_4);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_15);
lean_dec(x_2);
x_49 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_50 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_49, x_3, x_1);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; lean_object* x_52; 
x_51 = 0;
lean_inc(x_1);
x_52 = l_Lean_PrettyPrinter_Parenthesizer_compileParser(x_3, x_1, x_51, x_4);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind), 5, 1);
lean_closure_set(x_55, 0, x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_52, 0, x_56);
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_52, 0);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_52);
x_59 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind), 5, 1);
lean_closure_set(x_59, 0, x_1);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_52);
if (x_62 == 0)
{
return x_52;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_52, 0);
x_64 = lean_ctor_get(x_52, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_52);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_1);
x_66 = lean_ctor_get(x_50, 0);
lean_inc(x_66);
lean_dec(x_50);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_3);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_4);
return x_68;
}
}
}
}
}
lean_object* l_IO_ofExcept___at_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___rarg___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___rarg___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_ofExcept___at_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_numLitKind___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_numLitKind___closed__1;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__3;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed), 7, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__4;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__5;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_strLitKind___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_strLitKind___closed__1;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__7;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed), 7, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__8;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__9;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_charLitKind___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_charLitKind___closed__1;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__11;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed), 7, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__12;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__13;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_nameLitKind___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_nameLitKind___closed__1;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__15;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed), 7, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__16;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__17;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_identKind___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_identKind___closed__1;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__19;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed), 7, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__20;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__21;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_EIO_Monad___closed__1;
x_2 = l_StateT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__23;
x_2 = l_Lean_Name_inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_dec(x_1);
x_43 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_41, x_2, x_3);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_42, x_47, x_45);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 6, 2);
lean_closure_set(x_53, 0, x_46);
lean_closure_set(x_53, 1, x_52);
lean_ctor_set(x_50, 0, x_53);
return x_48;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 6, 2);
lean_closure_set(x_56, 0, x_46);
lean_closure_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_48, 0, x_57);
return x_48;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_48, 0);
x_59 = lean_ctor_get(x_48, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_48);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_62 = x_58;
} else {
 lean_dec_ref(x_58);
 x_62 = lean_box(0);
}
x_63 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 6, 2);
lean_closure_set(x_63, 0, x_46);
lean_closure_set(x_63, 1, x_60);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_59);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_46);
x_66 = !lean_is_exclusive(x_48);
if (x_66 == 0)
{
return x_48;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_48, 0);
x_68 = lean_ctor_get(x_48, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_48);
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
lean_dec(x_42);
x_70 = !lean_is_exclusive(x_43);
if (x_70 == 0)
{
return x_43;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_43, 0);
x_72 = lean_ctor_get(x_43, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_43);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
case 1:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_1, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_1, 1);
lean_inc(x_75);
lean_dec(x_1);
x_76 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_74, x_2, x_3);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_75, x_80, x_78);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 6, 2);
lean_closure_set(x_86, 0, x_79);
lean_closure_set(x_86, 1, x_85);
lean_ctor_set(x_83, 0, x_86);
return x_81;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_83, 0);
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_83);
x_89 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 6, 2);
lean_closure_set(x_89, 0, x_79);
lean_closure_set(x_89, 1, x_87);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
lean_ctor_set(x_81, 0, x_90);
return x_81;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_91 = lean_ctor_get(x_81, 0);
x_92 = lean_ctor_get(x_81, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_81);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_95 = x_91;
} else {
 lean_dec_ref(x_91);
 x_95 = lean_box(0);
}
x_96 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 6, 2);
lean_closure_set(x_96, 0, x_79);
lean_closure_set(x_96, 1, x_93);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_92);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_79);
x_99 = !lean_is_exclusive(x_81);
if (x_99 == 0)
{
return x_81;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_81, 0);
x_101 = lean_ctor_get(x_81, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_81);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_75);
x_103 = !lean_is_exclusive(x_76);
if (x_103 == 0)
{
return x_76;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_76, 0);
x_105 = lean_ctor_get(x_76, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_76);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
case 2:
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_1, 0);
lean_inc(x_107);
lean_dec(x_1);
x_108 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_107, x_2, x_3);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_110, 0);
x_113 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_optional_parenthesizer), 5, 1);
lean_closure_set(x_113, 0, x_112);
lean_ctor_set(x_110, 0, x_113);
return x_108;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_110, 0);
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_110);
x_116 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_optional_parenthesizer), 5, 1);
lean_closure_set(x_116, 0, x_114);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
lean_ctor_set(x_108, 0, x_117);
return x_108;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_118 = lean_ctor_get(x_108, 0);
x_119 = lean_ctor_get(x_108, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_108);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_122 = x_118;
} else {
 lean_dec_ref(x_118);
 x_122 = lean_box(0);
}
x_123 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_optional_parenthesizer), 5, 1);
lean_closure_set(x_123, 0, x_120);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_119);
return x_125;
}
}
else
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_108);
if (x_126 == 0)
{
return x_108;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_108, 0);
x_128 = lean_ctor_get(x_108, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_108);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
case 3:
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_1, 0);
lean_inc(x_130);
lean_dec(x_1);
x_131 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_130, x_2, x_3);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_131, 0);
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_133, 0);
x_136 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer), 5, 1);
lean_closure_set(x_136, 0, x_135);
lean_ctor_set(x_133, 0, x_136);
return x_131;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_133, 0);
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_133);
x_139 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer), 5, 1);
lean_closure_set(x_139, 0, x_137);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
lean_ctor_set(x_131, 0, x_140);
return x_131;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_141 = lean_ctor_get(x_131, 0);
x_142 = lean_ctor_get(x_131, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_131);
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_145 = x_141;
} else {
 lean_dec_ref(x_141);
 x_145 = lean_box(0);
}
x_146 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer), 5, 1);
lean_closure_set(x_146, 0, x_143);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_144);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_142);
return x_148;
}
}
else
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_131);
if (x_149 == 0)
{
return x_131;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_131, 0);
x_151 = lean_ctor_get(x_131, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_131);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
case 4:
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_1, 0);
lean_inc(x_153);
lean_dec(x_1);
x_154 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_153, x_2, x_3);
if (lean_obj_tag(x_154) == 0)
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
lean_object* x_156; uint8_t x_157; 
x_156 = lean_ctor_get(x_154, 0);
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_156, 0);
x_159 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_try_parenthesizer), 5, 1);
lean_closure_set(x_159, 0, x_158);
lean_ctor_set(x_156, 0, x_159);
return x_154;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_156, 0);
x_161 = lean_ctor_get(x_156, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_156);
x_162 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_try_parenthesizer), 5, 1);
lean_closure_set(x_162, 0, x_160);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
lean_ctor_set(x_154, 0, x_163);
return x_154;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_164 = lean_ctor_get(x_154, 0);
x_165 = lean_ctor_get(x_154, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_154);
x_166 = lean_ctor_get(x_164, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_168 = x_164;
} else {
 lean_dec_ref(x_164);
 x_168 = lean_box(0);
}
x_169 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_try_parenthesizer), 5, 1);
lean_closure_set(x_169, 0, x_166);
if (lean_is_scalar(x_168)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_168;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_167);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_165);
return x_171;
}
}
else
{
uint8_t x_172; 
x_172 = !lean_is_exclusive(x_154);
if (x_172 == 0)
{
return x_154;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_154, 0);
x_174 = lean_ctor_get(x_154, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_154);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
case 5:
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_1, 0);
lean_inc(x_176);
lean_dec(x_1);
x_177 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_176, x_2, x_3);
if (lean_obj_tag(x_177) == 0)
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
x_179 = lean_ctor_get(x_177, 0);
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_179, 0);
x_182 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer), 5, 1);
lean_closure_set(x_182, 0, x_181);
lean_ctor_set(x_179, 0, x_182);
return x_177;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_179, 0);
x_184 = lean_ctor_get(x_179, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_179);
x_185 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer), 5, 1);
lean_closure_set(x_185, 0, x_183);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
lean_ctor_set(x_177, 0, x_186);
return x_177;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_187 = lean_ctor_get(x_177, 0);
x_188 = lean_ctor_get(x_177, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_177);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_191 = x_187;
} else {
 lean_dec_ref(x_187);
 x_191 = lean_box(0);
}
x_192 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer), 5, 1);
lean_closure_set(x_192, 0, x_189);
if (lean_is_scalar(x_191)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_191;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_190);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_188);
return x_194;
}
}
else
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_177);
if (x_195 == 0)
{
return x_177;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_177, 0);
x_197 = lean_ctor_get(x_177, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_177);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
case 6:
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_1, 0);
lean_inc(x_199);
lean_dec(x_1);
x_200 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_199, x_2, x_3);
if (lean_obj_tag(x_200) == 0)
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_200);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = lean_ctor_get(x_200, 0);
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_202, 0);
x_205 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_many1_parenthesizer), 5, 1);
lean_closure_set(x_205, 0, x_204);
lean_ctor_set(x_202, 0, x_205);
return x_200;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_206 = lean_ctor_get(x_202, 0);
x_207 = lean_ctor_get(x_202, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_202);
x_208 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_many1_parenthesizer), 5, 1);
lean_closure_set(x_208, 0, x_206);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
lean_ctor_set(x_200, 0, x_209);
return x_200;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_210 = lean_ctor_get(x_200, 0);
x_211 = lean_ctor_get(x_200, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_200);
x_212 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_214 = x_210;
} else {
 lean_dec_ref(x_210);
 x_214 = lean_box(0);
}
x_215 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_many1_parenthesizer), 5, 1);
lean_closure_set(x_215, 0, x_212);
if (lean_is_scalar(x_214)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_214;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_213);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_211);
return x_217;
}
}
else
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_200);
if (x_218 == 0)
{
return x_200;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_200, 0);
x_220 = lean_ctor_get(x_200, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_200);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
case 7:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_1, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_1, 1);
lean_inc(x_223);
lean_dec(x_1);
x_224 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_222, x_2, x_3);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = lean_ctor_get(x_225, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_225, 1);
lean_inc(x_228);
lean_dec(x_225);
x_229 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_223, x_228, x_226);
if (lean_obj_tag(x_229) == 0)
{
uint8_t x_230; 
x_230 = !lean_is_exclusive(x_229);
if (x_230 == 0)
{
lean_object* x_231; uint8_t x_232; 
x_231 = lean_ctor_get(x_229, 0);
x_232 = !lean_is_exclusive(x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_231, 0);
x_234 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer), 6, 2);
lean_closure_set(x_234, 0, x_227);
lean_closure_set(x_234, 1, x_233);
lean_ctor_set(x_231, 0, x_234);
return x_229;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_235 = lean_ctor_get(x_231, 0);
x_236 = lean_ctor_get(x_231, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_231);
x_237 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer), 6, 2);
lean_closure_set(x_237, 0, x_227);
lean_closure_set(x_237, 1, x_235);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_236);
lean_ctor_set(x_229, 0, x_238);
return x_229;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_239 = lean_ctor_get(x_229, 0);
x_240 = lean_ctor_get(x_229, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_229);
x_241 = lean_ctor_get(x_239, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_239, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_243 = x_239;
} else {
 lean_dec_ref(x_239);
 x_243 = lean_box(0);
}
x_244 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer), 6, 2);
lean_closure_set(x_244, 0, x_227);
lean_closure_set(x_244, 1, x_241);
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_242);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_240);
return x_246;
}
}
else
{
uint8_t x_247; 
lean_dec(x_227);
x_247 = !lean_is_exclusive(x_229);
if (x_247 == 0)
{
return x_229;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_229, 0);
x_249 = lean_ctor_get(x_229, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_229);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
else
{
uint8_t x_251; 
lean_dec(x_223);
x_251 = !lean_is_exclusive(x_224);
if (x_251 == 0)
{
return x_224;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_224, 0);
x_253 = lean_ctor_get(x_224, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_224);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
case 8:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_1, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_1, 1);
lean_inc(x_256);
lean_dec(x_1);
x_257 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_255, x_2, x_3);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = lean_ctor_get(x_258, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_261);
lean_dec(x_258);
x_262 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_256, x_261, x_259);
if (lean_obj_tag(x_262) == 0)
{
uint8_t x_263; 
x_263 = !lean_is_exclusive(x_262);
if (x_263 == 0)
{
lean_object* x_264; uint8_t x_265; 
x_264 = lean_ctor_get(x_262, 0);
x_265 = !lean_is_exclusive(x_264);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_264, 0);
x_267 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_sepBy1_parenthesizer), 6, 2);
lean_closure_set(x_267, 0, x_260);
lean_closure_set(x_267, 1, x_266);
lean_ctor_set(x_264, 0, x_267);
return x_262;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_268 = lean_ctor_get(x_264, 0);
x_269 = lean_ctor_get(x_264, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_264);
x_270 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_sepBy1_parenthesizer), 6, 2);
lean_closure_set(x_270, 0, x_260);
lean_closure_set(x_270, 1, x_268);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_269);
lean_ctor_set(x_262, 0, x_271);
return x_262;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_272 = lean_ctor_get(x_262, 0);
x_273 = lean_ctor_get(x_262, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_262);
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_272, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_276 = x_272;
} else {
 lean_dec_ref(x_272);
 x_276 = lean_box(0);
}
x_277 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_sepBy1_parenthesizer), 6, 2);
lean_closure_set(x_277, 0, x_260);
lean_closure_set(x_277, 1, x_274);
if (lean_is_scalar(x_276)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_276;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_275);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_273);
return x_279;
}
}
else
{
uint8_t x_280; 
lean_dec(x_260);
x_280 = !lean_is_exclusive(x_262);
if (x_280 == 0)
{
return x_262;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_262, 0);
x_282 = lean_ctor_get(x_262, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_262);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
return x_283;
}
}
}
else
{
uint8_t x_284; 
lean_dec(x_256);
x_284 = !lean_is_exclusive(x_257);
if (x_284 == 0)
{
return x_257;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_257, 0);
x_286 = lean_ctor_get(x_257, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_257);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
return x_287;
}
}
}
case 9:
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_288 = lean_ctor_get(x_1, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_1, 1);
lean_inc(x_289);
x_290 = lean_ctor_get(x_1, 2);
lean_inc(x_290);
lean_dec(x_1);
x_291 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_290, x_2, x_3);
if (lean_obj_tag(x_291) == 0)
{
uint8_t x_292; 
x_292 = !lean_is_exclusive(x_291);
if (x_292 == 0)
{
lean_object* x_293; uint8_t x_294; 
x_293 = lean_ctor_get(x_291, 0);
x_294 = !lean_is_exclusive(x_293);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_293, 0);
x_296 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 7, 3);
lean_closure_set(x_296, 0, x_288);
lean_closure_set(x_296, 1, x_289);
lean_closure_set(x_296, 2, x_295);
lean_ctor_set(x_293, 0, x_296);
return x_291;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_297 = lean_ctor_get(x_293, 0);
x_298 = lean_ctor_get(x_293, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_293);
x_299 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 7, 3);
lean_closure_set(x_299, 0, x_288);
lean_closure_set(x_299, 1, x_289);
lean_closure_set(x_299, 2, x_297);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_298);
lean_ctor_set(x_291, 0, x_300);
return x_291;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_301 = lean_ctor_get(x_291, 0);
x_302 = lean_ctor_get(x_291, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_291);
x_303 = lean_ctor_get(x_301, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_301, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_305 = x_301;
} else {
 lean_dec_ref(x_301);
 x_305 = lean_box(0);
}
x_306 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 7, 3);
lean_closure_set(x_306, 0, x_288);
lean_closure_set(x_306, 1, x_289);
lean_closure_set(x_306, 2, x_303);
if (lean_is_scalar(x_305)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_305;
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_304);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_302);
return x_308;
}
}
else
{
uint8_t x_309; 
lean_dec(x_289);
lean_dec(x_288);
x_309 = !lean_is_exclusive(x_291);
if (x_309 == 0)
{
return x_291;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_291, 0);
x_311 = lean_ctor_get(x_291, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_291);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
return x_312;
}
}
}
case 10:
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_313 = lean_ctor_get(x_1, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_1, 1);
lean_inc(x_314);
x_315 = lean_ctor_get(x_1, 2);
lean_inc(x_315);
lean_dec(x_1);
x_316 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_315, x_2, x_3);
if (lean_obj_tag(x_316) == 0)
{
uint8_t x_317; 
x_317 = !lean_is_exclusive(x_316);
if (x_317 == 0)
{
lean_object* x_318; uint8_t x_319; 
x_318 = lean_ctor_get(x_316, 0);
x_319 = !lean_is_exclusive(x_318);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_318, 0);
x_321 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer), 7, 3);
lean_closure_set(x_321, 0, x_313);
lean_closure_set(x_321, 1, x_314);
lean_closure_set(x_321, 2, x_320);
lean_ctor_set(x_318, 0, x_321);
return x_316;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_322 = lean_ctor_get(x_318, 0);
x_323 = lean_ctor_get(x_318, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_318);
x_324 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer), 7, 3);
lean_closure_set(x_324, 0, x_313);
lean_closure_set(x_324, 1, x_314);
lean_closure_set(x_324, 2, x_322);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_323);
lean_ctor_set(x_316, 0, x_325);
return x_316;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_326 = lean_ctor_get(x_316, 0);
x_327 = lean_ctor_get(x_316, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_316);
x_328 = lean_ctor_get(x_326, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_326, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 x_330 = x_326;
} else {
 lean_dec_ref(x_326);
 x_330 = lean_box(0);
}
x_331 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer), 7, 3);
lean_closure_set(x_331, 0, x_313);
lean_closure_set(x_331, 1, x_314);
lean_closure_set(x_331, 2, x_328);
if (lean_is_scalar(x_330)) {
 x_332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_332 = x_330;
}
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_329);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_327);
return x_333;
}
}
else
{
uint8_t x_334; 
lean_dec(x_314);
lean_dec(x_313);
x_334 = !lean_is_exclusive(x_316);
if (x_334 == 0)
{
return x_316;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_316, 0);
x_336 = lean_ctor_get(x_316, 1);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_316);
x_337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_336);
return x_337;
}
}
}
case 11:
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_1);
x_338 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__1;
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_2);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_3);
return x_340;
}
case 12:
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_1);
x_341 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__2;
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_2);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_3);
return x_343;
}
case 13:
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__6;
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_2);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_3);
return x_346;
}
case 14:
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__10;
x_348 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_2);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_3);
return x_349;
}
case 15:
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__14;
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_2);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_3);
return x_352;
}
case 16:
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_353 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__18;
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_2);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_3);
return x_355;
}
case 17:
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__22;
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_2);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_3);
return x_358;
}
case 18:
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_359 = lean_ctor_get(x_1, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_1, 1);
lean_inc(x_360);
lean_dec(x_1);
x_361 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer), 6, 2);
lean_closure_set(x_361, 0, x_359);
lean_closure_set(x_361, 1, x_360);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_2);
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_3);
return x_363;
}
default: 
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_364 = lean_ctor_get(x_1, 0);
lean_inc(x_364);
lean_dec(x_1);
x_365 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_366 = l_Lean_CombinatorCompilerAttribute_getDeclFor(x_365, x_2, x_364);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_367 = lean_box(0);
x_368 = l_Lean_mkConst(x_364, x_367);
x_369 = l_Lean_MetavarContext_Inhabited___closed__1;
x_370 = l_Lean_Meta_run___rarg___closed__5;
x_371 = l_Lean_NameGenerator_Inhabited___closed__3;
x_372 = l_Lean_TraceState_Inhabited___closed__1;
x_373 = l_Std_PersistentArray_empty___closed__3;
lean_inc(x_2);
x_374 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_374, 0, x_2);
lean_ctor_set(x_374, 1, x_369);
lean_ctor_set(x_374, 2, x_370);
lean_ctor_set(x_374, 3, x_371);
lean_ctor_set(x_374, 4, x_372);
lean_ctor_set(x_374, 5, x_373);
x_375 = l_Lean_PrettyPrinter_Parenthesizer_compileParser___closed__1;
x_376 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_368, x_375, x_374);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
lean_dec(x_376);
x_379 = lean_ctor_get(x_378, 4);
lean_inc(x_379);
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
lean_dec(x_379);
x_381 = l_Std_PersistentArray_forM___at_IO_runMeta___spec__3(x_380, x_3);
lean_dec(x_380);
if (lean_obj_tag(x_381) == 0)
{
if (lean_obj_tag(x_377) == 4)
{
uint8_t x_382; 
lean_dec(x_2);
x_382 = !lean_is_exclusive(x_381);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_383 = lean_ctor_get(x_381, 0);
lean_dec(x_383);
x_384 = lean_ctor_get(x_377, 0);
lean_inc(x_384);
lean_dec(x_377);
x_385 = lean_ctor_get(x_378, 0);
lean_inc(x_385);
lean_dec(x_378);
x_386 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_386, 0, x_384);
lean_ctor_set(x_386, 1, x_385);
lean_ctor_set(x_381, 0, x_386);
x_4 = x_381;
goto block_40;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_387 = lean_ctor_get(x_381, 1);
lean_inc(x_387);
lean_dec(x_381);
x_388 = lean_ctor_get(x_377, 0);
lean_inc(x_388);
lean_dec(x_377);
x_389 = lean_ctor_get(x_378, 0);
lean_inc(x_389);
lean_dec(x_378);
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_388);
lean_ctor_set(x_390, 1, x_389);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_387);
x_4 = x_391;
goto block_40;
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_378);
lean_dec(x_377);
x_392 = lean_ctor_get(x_381, 1);
lean_inc(x_392);
lean_dec(x_381);
x_393 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__24;
x_394 = l_unreachable_x21___rarg(x_393);
x_395 = lean_apply_2(x_394, x_2, x_392);
x_4 = x_395;
goto block_40;
}
}
else
{
uint8_t x_396; 
lean_dec(x_378);
lean_dec(x_377);
lean_dec(x_2);
x_396 = !lean_is_exclusive(x_381);
if (x_396 == 0)
{
x_4 = x_381;
goto block_40;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_381, 0);
x_398 = lean_ctor_get(x_381, 1);
lean_inc(x_398);
lean_inc(x_397);
lean_dec(x_381);
x_399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set(x_399, 1, x_398);
x_4 = x_399;
goto block_40;
}
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_dec(x_2);
x_400 = lean_ctor_get(x_376, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_376, 1);
lean_inc(x_401);
lean_dec(x_376);
x_402 = lean_ctor_get(x_401, 4);
lean_inc(x_402);
lean_dec(x_401);
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
lean_dec(x_402);
x_404 = l_Std_PersistentArray_forM___at_IO_runMeta___spec__3(x_403, x_3);
lean_dec(x_403);
if (lean_obj_tag(x_404) == 0)
{
uint8_t x_405; 
x_405 = !lean_is_exclusive(x_404);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_406 = lean_ctor_get(x_404, 0);
lean_dec(x_406);
x_407 = l_Lean_Meta_Exception_toStr(x_400);
x_408 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set_tag(x_404, 1);
lean_ctor_set(x_404, 0, x_408);
x_4 = x_404;
goto block_40;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_409 = lean_ctor_get(x_404, 1);
lean_inc(x_409);
lean_dec(x_404);
x_410 = l_Lean_Meta_Exception_toStr(x_400);
x_411 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_411, 0, x_410);
x_412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_409);
x_4 = x_412;
goto block_40;
}
}
else
{
uint8_t x_413; 
lean_dec(x_400);
x_413 = !lean_is_exclusive(x_404);
if (x_413 == 0)
{
x_4 = x_404;
goto block_40;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_404, 0);
x_415 = lean_ctor_get(x_404, 1);
lean_inc(x_415);
lean_inc(x_414);
lean_dec(x_404);
x_416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_415);
x_4 = x_416;
goto block_40;
}
}
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_364);
x_417 = lean_ctor_get(x_366, 0);
lean_inc(x_417);
lean_dec(x_366);
x_418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_2);
x_419 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_3);
x_4 = x_419;
goto block_40;
}
}
}
block_40:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
lean_inc(x_9);
x_11 = l_Lean_Environment_evalConstCheck___rarg(x_9, x_10, x_8);
x_12 = l_IO_ofExcept___at_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___spec__1(x_11, x_6);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_5, 0, x_14);
lean_ctor_set(x_12, 0, x_5);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_5, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_free_object(x_5);
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_24 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
lean_inc(x_23);
x_25 = l_Lean_Environment_evalConstCheck___rarg(x_23, x_24, x_22);
x_26 = l_IO_ofExcept___at_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___spec__1(x_25, x_6);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_23);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_23);
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_34 = x_26;
} else {
 lean_dec_ref(x_26);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_4);
if (x_36 == 0)
{
return x_4;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_4, 0);
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_4);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
lean_object* l_IO_ofExcept___at_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstantUnsafe___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_KeyedDeclsAttribute_Table_insert___rarg(x_5, x_1, x_2);
lean_ctor_set(x_3, 1, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = l_Lean_KeyedDeclsAttribute_Table_insert___rarg(x_8, x_1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstantUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_14; 
lean_inc(x_2);
lean_inc(x_1);
x_14 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_2);
x_17 = l_Lean_Environment_evalConstCheck___rarg___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Char_HasRepr___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = l_Lean_ConstantInfo_type(x_23);
lean_dec(x_23);
x_25 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8;
x_26 = l_Lean_Expr_isConstOf(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_28 = l_Lean_Expr_isConstOf(x_24, x_27);
lean_dec(x_24);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_eval_const(x_1, x_2);
x_30 = l_IO_ofExcept___at_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___spec__1(x_29, x_3);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_31, x_1, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_4 = x_34;
x_5 = x_35;
goto block_13;
}
else
{
uint8_t x_36; 
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
return x_30;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_30, 0);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_30);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_45 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_44, x_1, x_2);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; lean_object* x_47; 
x_46 = 0;
lean_inc(x_2);
x_47 = l_Lean_PrettyPrinter_Parenthesizer_compileParser(x_1, x_2, x_46, x_3);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_2);
x_50 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind), 5, 1);
lean_closure_set(x_50, 0, x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
x_4 = x_51;
x_5 = x_49;
goto block_13;
}
else
{
uint8_t x_52; 
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_47, 0);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_47);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_45, 0);
lean_inc(x_56);
lean_dec(x_45);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_1);
x_4 = x_57;
x_5 = x_3;
goto block_13;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_24);
x_58 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_59 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_58, x_1, x_2);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; lean_object* x_61; 
x_60 = 0;
lean_inc(x_2);
x_61 = l_Lean_PrettyPrinter_Parenthesizer_compileParser(x_1, x_2, x_60, x_3);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_2);
x_64 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind), 5, 1);
lean_closure_set(x_64, 0, x_2);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
x_4 = x_65;
x_5 = x_63;
goto block_13;
}
else
{
uint8_t x_66; 
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_61);
if (x_66 == 0)
{
return x_61;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_61, 0);
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_61);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_59, 0);
lean_inc(x_70);
lean_dec(x_59);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_1);
x_4 = x_71;
x_5 = x_3;
goto block_13;
}
}
}
block_13:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstantUnsafe___lambda__1), 3, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_6);
x_11 = l_Lean_PersistentEnvExtension_modifyState___rarg(x_9, x_7, x_10);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_Error_Inhabited___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_parenthesize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_box(0);
x_6 = l_Lean_Syntax_Traverser_fromSyntax(x_2);
x_7 = 0;
x_8 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_7);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_12 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 6);
x_13 = 1;
x_14 = l_Lean_Meta_TransparencyMode_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_apply_4(x_1, x_5, x_8, x_3, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
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
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; 
lean_ctor_set_uint8(x_10, sizeof(void*)*1 + 6, x_13);
x_29 = lean_apply_4(x_1, x_5, x_8, x_3, x_4);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_29, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
lean_ctor_set(x_29, 0, x_35);
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_29);
if (x_39 == 0)
{
return x_29;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_29, 0);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_29);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; 
x_43 = lean_ctor_get(x_10, 0);
x_44 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
x_45 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 1);
x_46 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 2);
x_47 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 3);
x_48 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 4);
x_49 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 5);
x_50 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 6);
lean_inc(x_43);
lean_dec(x_10);
x_51 = 1;
x_52 = l_Lean_Meta_TransparencyMode_lt(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_53, 0, x_43);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_44);
lean_ctor_set_uint8(x_53, sizeof(void*)*1 + 1, x_45);
lean_ctor_set_uint8(x_53, sizeof(void*)*1 + 2, x_46);
lean_ctor_set_uint8(x_53, sizeof(void*)*1 + 3, x_47);
lean_ctor_set_uint8(x_53, sizeof(void*)*1 + 4, x_48);
lean_ctor_set_uint8(x_53, sizeof(void*)*1 + 5, x_49);
lean_ctor_set_uint8(x_53, sizeof(void*)*1 + 6, x_50);
lean_ctor_set(x_3, 0, x_53);
x_54 = lean_apply_4(x_1, x_5, x_8, x_3, x_4);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_59 = x_54;
} else {
 lean_dec_ref(x_54);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
lean_dec(x_57);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_54, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_64 = x_54;
} else {
 lean_dec_ref(x_54);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_66, 0, x_43);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_44);
lean_ctor_set_uint8(x_66, sizeof(void*)*1 + 1, x_45);
lean_ctor_set_uint8(x_66, sizeof(void*)*1 + 2, x_46);
lean_ctor_set_uint8(x_66, sizeof(void*)*1 + 3, x_47);
lean_ctor_set_uint8(x_66, sizeof(void*)*1 + 4, x_48);
lean_ctor_set_uint8(x_66, sizeof(void*)*1 + 5, x_49);
lean_ctor_set_uint8(x_66, sizeof(void*)*1 + 6, x_51);
lean_ctor_set(x_3, 0, x_66);
x_67 = lean_apply_4(x_1, x_5, x_8, x_3, x_4);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_72 = x_67;
} else {
 lean_dec_ref(x_67);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_70, 0);
lean_inc(x_73);
lean_dec(x_70);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_67, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_67, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_77 = x_67;
} else {
 lean_dec_ref(x_67);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; lean_object* x_92; uint8_t x_93; uint8_t x_94; 
x_79 = lean_ctor_get(x_3, 0);
x_80 = lean_ctor_get(x_3, 1);
x_81 = lean_ctor_get(x_3, 2);
x_82 = lean_ctor_get(x_3, 3);
x_83 = lean_ctor_get(x_3, 4);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_3);
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
x_85 = lean_ctor_get_uint8(x_79, sizeof(void*)*1);
x_86 = lean_ctor_get_uint8(x_79, sizeof(void*)*1 + 1);
x_87 = lean_ctor_get_uint8(x_79, sizeof(void*)*1 + 2);
x_88 = lean_ctor_get_uint8(x_79, sizeof(void*)*1 + 3);
x_89 = lean_ctor_get_uint8(x_79, sizeof(void*)*1 + 4);
x_90 = lean_ctor_get_uint8(x_79, sizeof(void*)*1 + 5);
x_91 = lean_ctor_get_uint8(x_79, sizeof(void*)*1 + 6);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_92 = x_79;
} else {
 lean_dec_ref(x_79);
 x_92 = lean_box(0);
}
x_93 = 1;
x_94 = l_Lean_Meta_TransparencyMode_lt(x_91, x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
if (lean_is_scalar(x_92)) {
 x_95 = lean_alloc_ctor(0, 1, 7);
} else {
 x_95 = x_92;
}
lean_ctor_set(x_95, 0, x_84);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_85);
lean_ctor_set_uint8(x_95, sizeof(void*)*1 + 1, x_86);
lean_ctor_set_uint8(x_95, sizeof(void*)*1 + 2, x_87);
lean_ctor_set_uint8(x_95, sizeof(void*)*1 + 3, x_88);
lean_ctor_set_uint8(x_95, sizeof(void*)*1 + 4, x_89);
lean_ctor_set_uint8(x_95, sizeof(void*)*1 + 5, x_90);
lean_ctor_set_uint8(x_95, sizeof(void*)*1 + 6, x_91);
x_96 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_80);
lean_ctor_set(x_96, 2, x_81);
lean_ctor_set(x_96, 3, x_82);
lean_ctor_set(x_96, 4, x_83);
x_97 = lean_apply_4(x_1, x_5, x_8, x_96, x_4);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_102 = x_97;
} else {
 lean_dec_ref(x_97);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_100, 0);
lean_inc(x_103);
lean_dec(x_100);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_97, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_97, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_107 = x_97;
} else {
 lean_dec_ref(x_97);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
if (lean_is_scalar(x_92)) {
 x_109 = lean_alloc_ctor(0, 1, 7);
} else {
 x_109 = x_92;
}
lean_ctor_set(x_109, 0, x_84);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_85);
lean_ctor_set_uint8(x_109, sizeof(void*)*1 + 1, x_86);
lean_ctor_set_uint8(x_109, sizeof(void*)*1 + 2, x_87);
lean_ctor_set_uint8(x_109, sizeof(void*)*1 + 3, x_88);
lean_ctor_set_uint8(x_109, sizeof(void*)*1 + 4, x_89);
lean_ctor_set_uint8(x_109, sizeof(void*)*1 + 5, x_90);
lean_ctor_set_uint8(x_109, sizeof(void*)*1 + 6, x_93);
x_110 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_80);
lean_ctor_set(x_110, 2, x_81);
lean_ctor_set(x_110, 3, x_82);
lean_ctor_set(x_110, 4, x_83);
x_111 = lean_apply_4(x_1, x_5, x_8, x_110, x_4);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec(x_113);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_116 = x_111;
} else {
 lean_dec_ref(x_111);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
lean_dec(x_114);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_111, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_111, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_121 = x_111;
} else {
 lean_dec_ref(x_111);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
}
}
lean_object* _init_l_Lean_PrettyPrinter_parenthesizeTerm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_termParser___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_parenthesizeTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_PrettyPrinter_parenthesizeTerm___closed__1;
x_5 = l_Lean_PrettyPrinter_parenthesize(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_parenthesizeCommand___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("command");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_parenthesizeCommand___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_parenthesizeCommand___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_parenthesizeCommand___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_parenthesizeCommand___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_parenthesizeCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_PrettyPrinter_parenthesizeCommand___closed__3;
x_5 = l_Lean_PrettyPrinter_parenthesize(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l___private_Lean_PrettyPrinter_Parenthesizer_1__regTraceClasses___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
if (x_4 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstantUnsafe(x_2, x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_compileParser(x_2, x_3, x_4, x_5);
return x_7;
}
}
}
lean_object* _init_l___private_Lean_PrettyPrinter_Parenthesizer_1__regTraceClasses___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_Parenthesizer_1__regTraceClasses___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* l___private_Lean_PrettyPrinter_Parenthesizer_1__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l___private_Lean_PrettyPrinter_Parenthesizer_1__regTraceClasses___closed__1;
x_6 = l_Lean_Parser_registerParserAttributeHook(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
return x_3;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l___private_Lean_PrettyPrinter_Parenthesizer_1__regTraceClasses___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l___private_Lean_PrettyPrinter_Parenthesizer_1__regTraceClasses___lambda__1(x_1, x_2, x_3, x_6, x_5);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_ReplaceExpr(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Lean_Meta_WHNF(lean_object*);
lean_object* initialize_Lean_KeyedDeclsAttribute(lean_object*);
lean_object* initialize_Lean_Parser_Extension(lean_object*);
lean_object* initialize_Lean_ParserCompiler(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_PrettyPrinter_Parenthesizer(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_KeyedDeclsAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Extension(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ParserCompiler(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__2);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__3);
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
l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__3 = _init_l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__3();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__3);
l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1___closed__1 = _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1___closed__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1___closed__1);
l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1___closed__2 = _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1___closed__2();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1___closed__2);
l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1 = _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1);
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
res = l_Lean_PrettyPrinter_mkParenthesizerAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_parenthesizerAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizerAttribute);
lean_dec_ref(res);
l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCategoryParenthesizerAttribute___lambda__1___closed__1);
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
l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__3 = _init_l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__3();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__3);
l_Lean_SMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__1___closed__1 = _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__1___closed__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__1___closed__1);
l_Lean_SMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__1___closed__2 = _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__1___closed__2();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__1___closed__2);
l_Lean_SMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__1 = _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_PrettyPrinter_categoryParenthesizerAttribute___spec__1);
l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__1 = _init_l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__1);
l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__2 = _init_l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__2);
l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__3 = _init_l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__3);
l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__4 = _init_l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__4);
l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__5 = _init_l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_categoryParenthesizerAttribute___closed__5);
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
l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__5 = _init_l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__5);
l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__6 = _init_l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__6);
l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__7 = _init_l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__7);
l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser = _init_l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser);
l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_monadQuotation = _init_l_Lean_PrettyPrinter_Parenthesizer_monadQuotation();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_monadQuotation);
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
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__22 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__22();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__22);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__23 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__23();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__23);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__24 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__24();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__24);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__25 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__25();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__25);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__26 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__26();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__26);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__27 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__27();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__27);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__28 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__28();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__28);
l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__29 = _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__29();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__29);
l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5 = _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5);
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
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___closed__4);
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
l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__7 = _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__7);
l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__8 = _init_l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__8);
l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__5 = _init_l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__5);
l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer___closed__1);
l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1 = _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1);
l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__2 = _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__2();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__2);
l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1 = _init_l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1();
lean_mark_persistent(l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__5 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__5);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__7 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__7);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__9 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__9);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__10 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__10);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__11 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__11);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__12 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__12);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__13 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__13();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__13);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__14 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__14();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__14);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__15 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__15();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__15);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__16 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__16();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__16);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__17 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__17();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__17);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__18 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__18();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__18);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__19 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__19();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__19);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__20 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__20();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__20);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__21 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__21();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__21);
l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__22 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__22();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__22);
l_Lean_PrettyPrinter_Parenthesizer_compileParser___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParser___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParser___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_compileParser___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParser___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParser___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___rarg___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___rarg___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___rarg___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__5 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__5);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__6 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__6);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__7 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__7);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__8 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__8);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__9 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__9);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__10 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__10);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__11 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__11);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__12 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__12);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__13 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__13();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__13);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__14 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__14();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__14);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__15 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__15();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__15);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__16 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__16();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__16);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__17 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__17();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__17);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__18 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__18();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__18);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__19 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__19();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__19);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__20 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__20();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__20);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__21 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__21();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__21);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__22 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__22();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__22);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__23 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__23();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__23);
l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__24 = _init_l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__24();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__24);
l_Lean_PrettyPrinter_parenthesizeTerm___closed__1 = _init_l_Lean_PrettyPrinter_parenthesizeTerm___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizeTerm___closed__1);
l_Lean_PrettyPrinter_parenthesizeCommand___closed__1 = _init_l_Lean_PrettyPrinter_parenthesizeCommand___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizeCommand___closed__1);
l_Lean_PrettyPrinter_parenthesizeCommand___closed__2 = _init_l_Lean_PrettyPrinter_parenthesizeCommand___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizeCommand___closed__2);
l_Lean_PrettyPrinter_parenthesizeCommand___closed__3 = _init_l_Lean_PrettyPrinter_parenthesizeCommand___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizeCommand___closed__3);
l___private_Lean_PrettyPrinter_Parenthesizer_1__regTraceClasses___closed__1 = _init_l___private_Lean_PrettyPrinter_Parenthesizer_1__regTraceClasses___closed__1();
lean_mark_persistent(l___private_Lean_PrettyPrinter_Parenthesizer_1__regTraceClasses___closed__1);
res = l___private_Lean_PrettyPrinter_Parenthesizer_1__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
