// Lean compiler output
// Module: Lean.PrettyPrinter.Parenthesizer
// Imports: Init Lean.Meta Lean.KeyedDeclsAttribute
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
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__9;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__3;
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14;
lean_object* l_Lean_fmt___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__5(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__28;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__11;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant___closed__1;
extern lean_object* l_Option_HasRepr___rarg___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__25;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer(lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__1;
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__9;
extern lean_object* l_Lean_identKind___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__2(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__17;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___boxed(lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__8;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__4;
lean_object* l_Lean_Syntax_Traverser_up(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__10;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__19;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeCommand___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___rarg___closed__1;
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__11;
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4(lean_object*);
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__7;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__24;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___closed__1;
extern lean_object* l_Lean_charLitKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__2;
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__4;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__20;
lean_object* l_ReaderT_Monad___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__15;
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__18;
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__5;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__7;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_charLitKind___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__21;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_parenthesizeCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeTerm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__13;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__5;
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkPrec_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer___boxed(lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_monadQuotation___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__11;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__4;
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__17;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__3;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1(size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__3;
lean_object* l_Lean_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__1___closed__2;
lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__3;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__23;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__7;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
lean_object* l_Lean_PrettyPrinter_parenthesizeCommand___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Option_format___rarg___closed__1;
lean_object* l_Lean_SMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__13;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__23;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___closed__1;
lean_object* l_Lean_Meta_throwOther___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_numLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___spec__1(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_fieldIdx_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Unhygienic_run___rarg(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__12;
extern lean_object* l_Lean_numLitKind___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_sepBy1_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParserOfStack_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
extern lean_object* l_Lean_Unhygienic_MonadQuotation___closed__4;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__21;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__21;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_strLitKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_charLitNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__19;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__4;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__1;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesize(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__22;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__17;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compile___closed__1;
lean_object* l_Lean_Meta_addContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_monadQuotation___spec__1(lean_object*);
lean_object* l_ReaderT_lift___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getValues___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__1;
extern lean_object* l_Lean_Environment_evalConstCheck___rarg___closed__1;
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_IO_ofExcept___at_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_attrParamSyntaxToIdentifier(lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__14;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__11;
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___boxed(lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__2;
lean_object* l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1___closed__2;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__13;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___boxed(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__16;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbol_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__12;
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__3(lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__7;
lean_object* l_StateT_get___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__16(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__2;
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__15;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_visitToken___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__10;
extern lean_object* l_Lean_KeyedDeclsAttribute_Def_mkSimple___elambda__1___rarg___closed__2;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer(lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
extern lean_object* l_Lean_Meta_mkAuxName___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__14;
lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody_x27___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo___main(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l_StateT_get___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_pushNone_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__4;
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___closed__3;
extern lean_object* l_Substring_drop___closed__2;
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Message_toString___spec__1(lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_monadQuotation___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__19;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_down(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_empty___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkInitAttr___lambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_setExpected_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__18;
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkStackTop_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ite___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__2(lean_object*, lean_object*);
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
extern lean_object* l___private_Lean_Environment_14__throwUnexpectedType___rarg___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__4;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_add_attribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__3;
lean_object* l_Lean_SMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkNoImmediateColon_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1;
lean_object* l_Lean_Meta_lambdaTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeCommand___closed__1;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setEnv(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compile(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__12;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nonReservedSymbol_parenthesizer(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__1;
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__14;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__4(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__4;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer___boxed(lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forM___at_IO_runMeta___spec__3(lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
extern lean_object* l_PUnit_Inhabited;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__3;
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_nameLitNoAntiquot_parenthesizer(lean_object*);
extern lean_object* l_Lean_Option_format___rarg___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__16;
lean_object* l_Lean_Meta_getConstInfo(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_optional_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoWs_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___closed__2;
lean_object* l_Lean_Meta_Exception_toStr(lean_object*);
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__15;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoWs_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nameLitKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___closed__3;
extern lean_object* l___private_Lean_Environment_14__throwUnexpectedType___rarg___closed__1;
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___closed__4;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___boxed(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
lean_object* l_Lean_ConstantInfo_value_x21(lean_object*);
lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__6;
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_monadQuotation___closed__3;
extern lean_object* l_Lean_MessageData_coeOfOptExpr___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__1;
lean_object* l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_parenthesizerAttribute___spec__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unquotedSymbol_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Environment_14__throwUnexpectedType___rarg___closed__2;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__20;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__6;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeTerm___closed__1;
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__4;
lean_object* l_Lean_Syntax_MonadTraverser_getIdx___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
extern lean_object* l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__1;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__2;
lean_object* l___private_Lean_PrettyPrinter_Parenthesizer_1__regTraceClasses(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_quotedSymbol_parenthesizer___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_symbolNoWs_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__15;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__18;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParserOfStack_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
lean_object* l_ReaderT_lift___at_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo___main(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_checkTailWs_parenthesizer___boxed(lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
lean_object* l_List_forM___main___at_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__16;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__5;
lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__1;
extern lean_object* l_Lean_Meta_addGlobalInstance___closed__3;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_strLitNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identEq_parenthesizer___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__26;
extern lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_identNoAntiquot_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__5;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___rarg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27(lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_Def_mkSimple(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_ParenthesizerM_monadTraverser;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_rawIdent_parenthesizer___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_unicodeSymbol_parenthesizer(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__2;
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkInitAttr___lambda__1___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_19; 
lean_inc(x_3);
x_19 = lean_environment_find(x_2, x_3);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
lean_dec(x_1);
x_20 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lean_ConstantInfo_type(x_22);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 4)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_name_eq(x_24, x_1);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_box(0);
x_5 = x_26;
goto block_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = l_Lean_mkConst(x_3, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_4);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_23);
x_30 = lean_box(0);
x_5 = x_30;
goto block_18;
}
}
block_18:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_3);
x_8 = l___private_Lean_Environment_14__throwUnexpectedType___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l___private_Lean_Environment_14__throwUnexpectedType___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Lean_Name_toStringWithSep___main(x_6, x_1);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = l___private_Lean_Environment_14__throwUnexpectedType___rarg___closed__3;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_attrParamSyntaxToIdentifier(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_KeyedDeclsAttribute_Def_mkSimple___elambda__1___rarg___closed__2;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesizer");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PrettyPrinter");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parenthesizer");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Register a parenthesizer for a parser.\n\n[parenthesizer k] registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` for the `SyntaxNodeKind` `k`.");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__2___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__3;
x_3 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_4 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__11;
x_5 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
x_6 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__10;
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__12;
x_8 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_4);
lean_ctor_set(x_8, 3, x_5);
lean_ctor_set(x_8, 4, x_1);
lean_ctor_set(x_8, 5, x_6);
lean_ctor_set(x_8, 6, x_7);
return x_8;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesizerAttribute");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__13;
x_3 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__15;
x_4 = l_Lean_KeyedDeclsAttribute_init___rarg(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
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
lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
x_3 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__3;
x_4 = l_Lean_KeyedDeclsAttribute_Def_mkSimple(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("combinatorParenthesizerAttribute");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__7;
x_2 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__4;
x_3 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__6;
x_4 = l_Lean_KeyedDeclsAttribute_init___rarg(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Std_mkHashMap___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_SMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__1___closed__1;
x_3 = l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__1___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_SMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__3;
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
lean_object* _init_l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1;
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("parenthesize");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__3;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__2;
x_2 = l_PUnit_Inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
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
x_2 = lean_unsigned_to_nat(166u);
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
x_1 = lean_unsigned_to_nat(1024u);
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
x_1 = l_Substring_drop___closed__2;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__26;
x_2 = l_Lean_MessageData_coeOfOptExpr___closed__1;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__27;
x_2 = l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__4;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
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
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_433; lean_object* x_434; lean_object* x_475; uint8_t x_476; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
x_21 = lean_box(0);
x_22 = 0;
x_23 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set(x_23, 3, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*4, x_22);
x_475 = lean_ctor_get(x_16, 4);
lean_inc(x_475);
x_476 = lean_ctor_get_uint8(x_475, sizeof(void*)*1);
lean_dec(x_475);
if (x_476 == 0)
{
lean_object* x_477; 
x_477 = lean_box(x_22);
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_477);
x_433 = x_14;
x_434 = x_16;
goto block_474;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_478 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_479 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_478, x_6, x_16);
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_479, 1);
lean_inc(x_481);
lean_dec(x_479);
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_480);
x_433 = x_14;
x_434 = x_481;
goto block_474;
}
block_432:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_1);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_1);
lean_inc(x_6);
x_28 = lean_apply_4(x_3, x_27, x_26, x_6, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
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
x_32 = lean_ctor_get(x_30, 2);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_31);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6;
x_35 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__9;
x_36 = lean_panic_fn(x_34, x_35);
x_37 = lean_apply_4(x_36, x_4, x_30, x_6, x_33);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_422; 
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_39 = x_28;
} else {
 lean_dec_ref(x_28);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_30, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_42 = x_32;
} else {
 lean_dec_ref(x_32);
 x_42 = lean_box(0);
}
x_422 = lean_nat_dec_lt(x_41, x_2);
if (x_422 == 0)
{
if (lean_obj_tag(x_40) == 0)
{
x_43 = x_422;
goto block_421;
}
else
{
lean_object* x_423; 
x_423 = lean_ctor_get(x_15, 1);
lean_inc(x_423);
if (lean_obj_tag(x_423) == 0)
{
x_43 = x_422;
goto block_421;
}
else
{
lean_object* x_424; lean_object* x_425; uint8_t x_426; 
x_424 = lean_ctor_get(x_40, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 0);
lean_inc(x_425);
lean_dec(x_423);
x_426 = lean_nat_dec_le(x_424, x_425);
lean_dec(x_425);
lean_dec(x_424);
x_43 = x_426;
goto block_421;
}
}
}
else
{
uint8_t x_427; 
x_427 = 1;
x_43 = x_427;
goto block_421;
}
block_421:
{
uint8_t x_44; 
if (x_43 == 0)
{
x_44 = x_22;
goto block_419;
}
else
{
uint8_t x_420; 
x_420 = 1;
x_44 = x_420;
goto block_419;
}
block_419:
{
lean_object* x_45; lean_object* x_46; lean_object* x_135; lean_object* x_136; lean_object* x_186; lean_object* x_187; lean_object* x_257; lean_object* x_258; lean_object* x_374; lean_object* x_375; lean_object* x_410; uint8_t x_411; 
x_410 = lean_ctor_get(x_38, 4);
lean_inc(x_410);
x_411 = lean_ctor_get_uint8(x_410, sizeof(void*)*1);
lean_dec(x_410);
if (x_411 == 0)
{
lean_object* x_412; lean_object* x_413; 
x_412 = lean_box(x_22);
if (lean_is_scalar(x_31)) {
 x_413 = lean_alloc_ctor(0, 2, 0);
} else {
 x_413 = x_31;
}
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_30);
x_374 = x_413;
x_375 = x_38;
goto block_409;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_414 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_415 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_414, x_6, x_38);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
lean_dec(x_415);
if (lean_is_scalar(x_31)) {
 x_418 = lean_alloc_ctor(0, 2, 0);
} else {
 x_418 = x_31;
}
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_30);
x_374 = x_418;
x_375 = x_417;
goto block_409;
}
block_134:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_47, x_6, x_46);
lean_dec(x_6);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_49, 1);
x_52 = lean_ctor_get(x_49, 0);
lean_dec(x_52);
x_53 = lean_ctor_get_uint8(x_15, sizeof(void*)*4);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_48, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_51);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_51, 3);
lean_dec(x_57);
x_58 = lean_ctor_get(x_51, 2);
lean_dec(x_58);
x_59 = lean_ctor_get(x_51, 1);
lean_dec(x_59);
if (lean_is_scalar(x_42)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_42;
}
lean_ctor_set(x_60, 0, x_2);
x_61 = lean_ctor_get(x_15, 2);
lean_inc(x_61);
lean_dec(x_15);
x_62 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
lean_ctor_set(x_51, 3, x_60);
lean_ctor_set(x_51, 2, x_61);
lean_ctor_set(x_51, 1, x_62);
x_63 = lean_box(0);
lean_ctor_set(x_49, 0, x_63);
return x_48;
}
else
{
lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_51, 0);
x_65 = lean_ctor_get_uint8(x_51, sizeof(void*)*4);
lean_inc(x_64);
lean_dec(x_51);
if (lean_is_scalar(x_42)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_42;
}
lean_ctor_set(x_66, 0, x_2);
x_67 = lean_ctor_get(x_15, 2);
lean_inc(x_67);
lean_dec(x_15);
x_68 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
x_69 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_67);
lean_ctor_set(x_69, 3, x_66);
lean_ctor_set_uint8(x_69, sizeof(void*)*4, x_65);
x_70 = lean_box(0);
lean_ctor_set(x_49, 1, x_69);
lean_ctor_set(x_49, 0, x_70);
return x_48;
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_71 = lean_ctor_get(x_48, 1);
lean_inc(x_71);
lean_dec(x_48);
x_72 = lean_ctor_get(x_51, 0);
lean_inc(x_72);
x_73 = lean_ctor_get_uint8(x_51, sizeof(void*)*4);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 x_74 = x_51;
} else {
 lean_dec_ref(x_51);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_42;
}
lean_ctor_set(x_75, 0, x_2);
x_76 = lean_ctor_get(x_15, 2);
lean_inc(x_76);
lean_dec(x_15);
x_77 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
if (lean_is_scalar(x_74)) {
 x_78 = lean_alloc_ctor(0, 4, 1);
} else {
 x_78 = x_74;
}
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_78, 2, x_76);
lean_ctor_set(x_78, 3, x_75);
lean_ctor_set_uint8(x_78, sizeof(void*)*4, x_73);
x_79 = lean_box(0);
lean_ctor_set(x_49, 1, x_78);
lean_ctor_set(x_49, 0, x_79);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_49);
lean_ctor_set(x_80, 1, x_71);
return x_80;
}
}
else
{
uint8_t x_81; 
lean_dec(x_42);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_48);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_48, 0);
lean_dec(x_82);
x_83 = !lean_is_exclusive(x_51);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_84 = lean_ctor_get(x_51, 3);
lean_dec(x_84);
x_85 = lean_ctor_get(x_51, 2);
lean_dec(x_85);
x_86 = lean_ctor_get(x_51, 1);
lean_dec(x_86);
x_87 = lean_ctor_get(x_15, 3);
lean_inc(x_87);
x_88 = lean_ctor_get(x_15, 2);
lean_inc(x_88);
lean_dec(x_15);
x_89 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
lean_ctor_set(x_51, 3, x_87);
lean_ctor_set(x_51, 2, x_88);
lean_ctor_set(x_51, 1, x_89);
x_90 = lean_box(0);
lean_ctor_set(x_49, 0, x_90);
return x_48;
}
else
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = lean_ctor_get(x_51, 0);
x_92 = lean_ctor_get_uint8(x_51, sizeof(void*)*4);
lean_inc(x_91);
lean_dec(x_51);
x_93 = lean_ctor_get(x_15, 3);
lean_inc(x_93);
x_94 = lean_ctor_get(x_15, 2);
lean_inc(x_94);
lean_dec(x_15);
x_95 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
x_96 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_96, 0, x_91);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_94);
lean_ctor_set(x_96, 3, x_93);
lean_ctor_set_uint8(x_96, sizeof(void*)*4, x_92);
x_97 = lean_box(0);
lean_ctor_set(x_49, 1, x_96);
lean_ctor_set(x_49, 0, x_97);
return x_48;
}
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_98 = lean_ctor_get(x_48, 1);
lean_inc(x_98);
lean_dec(x_48);
x_99 = lean_ctor_get(x_51, 0);
lean_inc(x_99);
x_100 = lean_ctor_get_uint8(x_51, sizeof(void*)*4);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 x_101 = x_51;
} else {
 lean_dec_ref(x_51);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get(x_15, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_15, 2);
lean_inc(x_103);
lean_dec(x_15);
x_104 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
if (lean_is_scalar(x_101)) {
 x_105 = lean_alloc_ctor(0, 4, 1);
} else {
 x_105 = x_101;
}
lean_ctor_set(x_105, 0, x_99);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_105, 2, x_103);
lean_ctor_set(x_105, 3, x_102);
lean_ctor_set_uint8(x_105, sizeof(void*)*4, x_100);
x_106 = lean_box(0);
lean_ctor_set(x_49, 1, x_105);
lean_ctor_set(x_49, 0, x_106);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_49);
lean_ctor_set(x_107, 1, x_98);
return x_107;
}
}
}
else
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_49, 1);
lean_inc(x_108);
lean_dec(x_49);
x_109 = lean_ctor_get_uint8(x_15, sizeof(void*)*4);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_110 = lean_ctor_get(x_48, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_111 = x_48;
} else {
 lean_dec_ref(x_48);
 x_111 = lean_box(0);
}
x_112 = lean_ctor_get(x_108, 0);
lean_inc(x_112);
x_113 = lean_ctor_get_uint8(x_108, sizeof(void*)*4);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 lean_ctor_release(x_108, 2);
 lean_ctor_release(x_108, 3);
 x_114 = x_108;
} else {
 lean_dec_ref(x_108);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_115 = lean_alloc_ctor(1, 1, 0);
} else {
 x_115 = x_42;
}
lean_ctor_set(x_115, 0, x_2);
x_116 = lean_ctor_get(x_15, 2);
lean_inc(x_116);
lean_dec(x_15);
x_117 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
if (lean_is_scalar(x_114)) {
 x_118 = lean_alloc_ctor(0, 4, 1);
} else {
 x_118 = x_114;
}
lean_ctor_set(x_118, 0, x_112);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_118, 2, x_116);
lean_ctor_set(x_118, 3, x_115);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_113);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
if (lean_is_scalar(x_111)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_111;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_110);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_42);
lean_dec(x_2);
x_122 = lean_ctor_get(x_48, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_123 = x_48;
} else {
 lean_dec_ref(x_48);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_108, 0);
lean_inc(x_124);
x_125 = lean_ctor_get_uint8(x_108, sizeof(void*)*4);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 lean_ctor_release(x_108, 2);
 lean_ctor_release(x_108, 3);
 x_126 = x_108;
} else {
 lean_dec_ref(x_108);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_15, 3);
lean_inc(x_127);
x_128 = lean_ctor_get(x_15, 2);
lean_inc(x_128);
lean_dec(x_15);
x_129 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
if (lean_is_scalar(x_126)) {
 x_130 = lean_alloc_ctor(0, 4, 1);
} else {
 x_130 = x_126;
}
lean_ctor_set(x_130, 0, x_124);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_130, 2, x_128);
lean_ctor_set(x_130, 3, x_127);
lean_ctor_set_uint8(x_130, sizeof(void*)*4, x_125);
x_131 = lean_box(0);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
if (lean_is_scalar(x_123)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_123;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_122);
return x_133;
}
}
}
block_185:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_137, x_6, x_136);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_ctor_get(x_140, 4);
lean_inc(x_141);
x_142 = lean_ctor_get_uint8(x_141, sizeof(void*)*1);
lean_dec(x_141);
if (x_142 == 0)
{
uint8_t x_143; 
lean_dec(x_4);
x_143 = !lean_is_exclusive(x_139);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_139, 0);
lean_dec(x_144);
x_145 = lean_box(0);
lean_ctor_set(x_139, 0, x_145);
x_45 = x_139;
x_46 = x_140;
goto block_134;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_139, 1);
lean_inc(x_146);
lean_dec(x_139);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
x_45 = x_148;
x_46 = x_140;
goto block_134;
}
}
else
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_139);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_150 = lean_ctor_get(x_139, 0);
x_151 = lean_ctor_get(x_139, 1);
x_152 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_153 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_152, x_6, x_140);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_unbox(x_154);
lean_dec(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_150);
lean_dec(x_4);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec(x_153);
x_157 = lean_box(0);
lean_ctor_set(x_139, 0, x_157);
x_45 = x_139;
x_46 = x_156;
goto block_134;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_free_object(x_139);
x_158 = lean_ctor_get(x_153, 1);
lean_inc(x_158);
lean_dec(x_153);
x_159 = lean_unsigned_to_nat(0u);
x_160 = l_Lean_Syntax_formatStxAux___main(x_21, x_22, x_159, x_150);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_163 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
x_164 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_152, x_163, x_4, x_151, x_6, x_158);
lean_dec(x_4);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_45 = x_165;
x_46 = x_166;
goto block_134;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_167 = lean_ctor_get(x_139, 0);
x_168 = lean_ctor_get(x_139, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_139);
x_169 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_170 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_169, x_6, x_140);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_unbox(x_171);
lean_dec(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_167);
lean_dec(x_4);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec(x_170);
x_174 = lean_box(0);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_168);
x_45 = x_175;
x_46 = x_173;
goto block_134;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_176 = lean_ctor_get(x_170, 1);
lean_inc(x_176);
lean_dec(x_170);
x_177 = lean_unsigned_to_nat(0u);
x_178 = l_Lean_Syntax_formatStxAux___main(x_21, x_22, x_177, x_167);
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_178);
x_180 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_181 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
x_182 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_169, x_181, x_4, x_168, x_6, x_176);
lean_dec(x_4);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_45 = x_183;
x_46 = x_184;
goto block_134;
}
}
}
}
block_256:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_188, x_6, x_187);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_ctor_get(x_190, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
lean_dec(x_190);
x_194 = l_Lean_Syntax_getHeadInfo___main(x_192);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_195 = lean_apply_1(x_1, x_192);
x_196 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_195, x_4, x_193, x_6, x_191);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_135 = x_197;
x_136 = x_198;
goto block_185;
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_194, 0);
lean_inc(x_199);
lean_dec(x_194);
x_200 = l_Lean_Syntax_getTailInfo___main(x_192);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_199);
x_201 = lean_apply_1(x_1, x_192);
x_202 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_201, x_4, x_193, x_6, x_191);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_135 = x_203;
x_136 = x_204;
goto block_185;
}
else
{
lean_object* x_205; uint8_t x_206; 
x_205 = lean_ctor_get(x_200, 0);
lean_inc(x_205);
lean_dec(x_200);
x_206 = !lean_is_exclusive(x_199);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_207 = lean_ctor_get(x_199, 0);
x_208 = lean_ctor_get(x_199, 1);
x_209 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14;
lean_inc(x_208);
lean_ctor_set(x_199, 0, x_209);
x_210 = l_Lean_Syntax_setHeadInfo(x_192, x_199);
x_211 = !lean_is_exclusive(x_205);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_212 = lean_ctor_get(x_205, 1);
x_213 = lean_ctor_get(x_205, 2);
lean_inc(x_212);
lean_ctor_set(x_205, 2, x_209);
x_214 = l_Lean_Syntax_setTailInfo(x_210, x_205);
x_215 = lean_apply_1(x_1, x_214);
x_216 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_216, 0, x_207);
lean_ctor_set(x_216, 1, x_208);
lean_ctor_set(x_216, 2, x_209);
x_217 = l_Lean_Syntax_setHeadInfo(x_215, x_216);
x_218 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_218, 0, x_209);
lean_ctor_set(x_218, 1, x_212);
lean_ctor_set(x_218, 2, x_213);
x_219 = l_Lean_Syntax_setTailInfo(x_217, x_218);
x_220 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_219, x_4, x_193, x_6, x_191);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_135 = x_221;
x_136 = x_222;
goto block_185;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_223 = lean_ctor_get(x_205, 0);
x_224 = lean_ctor_get(x_205, 1);
x_225 = lean_ctor_get(x_205, 2);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_205);
lean_inc(x_224);
x_226 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_224);
lean_ctor_set(x_226, 2, x_209);
x_227 = l_Lean_Syntax_setTailInfo(x_210, x_226);
x_228 = lean_apply_1(x_1, x_227);
x_229 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_229, 0, x_207);
lean_ctor_set(x_229, 1, x_208);
lean_ctor_set(x_229, 2, x_209);
x_230 = l_Lean_Syntax_setHeadInfo(x_228, x_229);
x_231 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_231, 0, x_209);
lean_ctor_set(x_231, 1, x_224);
lean_ctor_set(x_231, 2, x_225);
x_232 = l_Lean_Syntax_setTailInfo(x_230, x_231);
x_233 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_232, x_4, x_193, x_6, x_191);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_135 = x_234;
x_136 = x_235;
goto block_185;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_236 = lean_ctor_get(x_199, 0);
x_237 = lean_ctor_get(x_199, 1);
x_238 = lean_ctor_get(x_199, 2);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_199);
x_239 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14;
lean_inc(x_237);
x_240 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_237);
lean_ctor_set(x_240, 2, x_238);
x_241 = l_Lean_Syntax_setHeadInfo(x_192, x_240);
x_242 = lean_ctor_get(x_205, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_205, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_205, 2);
lean_inc(x_244);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 x_245 = x_205;
} else {
 lean_dec_ref(x_205);
 x_245 = lean_box(0);
}
lean_inc(x_243);
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(0, 3, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_242);
lean_ctor_set(x_246, 1, x_243);
lean_ctor_set(x_246, 2, x_239);
x_247 = l_Lean_Syntax_setTailInfo(x_241, x_246);
x_248 = lean_apply_1(x_1, x_247);
x_249 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_249, 0, x_236);
lean_ctor_set(x_249, 1, x_237);
lean_ctor_set(x_249, 2, x_239);
x_250 = l_Lean_Syntax_setHeadInfo(x_248, x_249);
x_251 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_251, 0, x_239);
lean_ctor_set(x_251, 1, x_243);
lean_ctor_set(x_251, 2, x_244);
x_252 = l_Lean_Syntax_setTailInfo(x_250, x_251);
x_253 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_252, x_4, x_193, x_6, x_191);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_135 = x_254;
x_136 = x_255;
goto block_185;
}
}
}
}
block_373:
{
if (x_44 == 0)
{
uint8_t x_259; 
lean_dec(x_42);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_259 = !lean_is_exclusive(x_257);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_260 = lean_ctor_get(x_257, 1);
x_261 = lean_ctor_get(x_257, 0);
lean_dec(x_261);
x_262 = lean_ctor_get_uint8(x_15, sizeof(void*)*4);
if (x_262 == 0)
{
lean_object* x_263; 
x_263 = lean_ctor_get(x_260, 3);
lean_inc(x_263);
if (lean_obj_tag(x_263) == 0)
{
uint8_t x_264; 
x_264 = !lean_is_exclusive(x_260);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_265 = lean_ctor_get(x_260, 3);
lean_dec(x_265);
x_266 = lean_ctor_get(x_260, 2);
lean_dec(x_266);
x_267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_267, 0, x_2);
x_268 = lean_ctor_get(x_15, 2);
lean_inc(x_268);
lean_dec(x_15);
lean_ctor_set(x_260, 3, x_267);
lean_ctor_set(x_260, 2, x_268);
x_269 = lean_box(0);
lean_ctor_set(x_257, 0, x_269);
if (lean_is_scalar(x_39)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_39;
}
lean_ctor_set(x_270, 0, x_257);
lean_ctor_set(x_270, 1, x_258);
return x_270;
}
else
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_271 = lean_ctor_get(x_260, 0);
x_272 = lean_ctor_get(x_260, 1);
x_273 = lean_ctor_get_uint8(x_260, sizeof(void*)*4);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_260);
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_2);
x_275 = lean_ctor_get(x_15, 2);
lean_inc(x_275);
lean_dec(x_15);
x_276 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_276, 0, x_271);
lean_ctor_set(x_276, 1, x_272);
lean_ctor_set(x_276, 2, x_275);
lean_ctor_set(x_276, 3, x_274);
lean_ctor_set_uint8(x_276, sizeof(void*)*4, x_273);
x_277 = lean_box(0);
lean_ctor_set(x_257, 1, x_276);
lean_ctor_set(x_257, 0, x_277);
if (lean_is_scalar(x_39)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_39;
}
lean_ctor_set(x_278, 0, x_257);
lean_ctor_set(x_278, 1, x_258);
return x_278;
}
}
else
{
uint8_t x_279; 
x_279 = !lean_is_exclusive(x_260);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_280 = lean_ctor_get(x_260, 3);
lean_dec(x_280);
x_281 = lean_ctor_get(x_260, 2);
lean_dec(x_281);
x_282 = !lean_is_exclusive(x_263);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_283 = lean_ctor_get(x_263, 0);
x_284 = l_Nat_min(x_283, x_2);
lean_dec(x_2);
lean_dec(x_283);
lean_ctor_set(x_263, 0, x_284);
x_285 = lean_ctor_get(x_15, 2);
lean_inc(x_285);
lean_dec(x_15);
lean_ctor_set(x_260, 2, x_285);
x_286 = lean_box(0);
lean_ctor_set(x_257, 0, x_286);
if (lean_is_scalar(x_39)) {
 x_287 = lean_alloc_ctor(0, 2, 0);
} else {
 x_287 = x_39;
}
lean_ctor_set(x_287, 0, x_257);
lean_ctor_set(x_287, 1, x_258);
return x_287;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_288 = lean_ctor_get(x_263, 0);
lean_inc(x_288);
lean_dec(x_263);
x_289 = l_Nat_min(x_288, x_2);
lean_dec(x_2);
lean_dec(x_288);
x_290 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_290, 0, x_289);
x_291 = lean_ctor_get(x_15, 2);
lean_inc(x_291);
lean_dec(x_15);
lean_ctor_set(x_260, 3, x_290);
lean_ctor_set(x_260, 2, x_291);
x_292 = lean_box(0);
lean_ctor_set(x_257, 0, x_292);
if (lean_is_scalar(x_39)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_39;
}
lean_ctor_set(x_293, 0, x_257);
lean_ctor_set(x_293, 1, x_258);
return x_293;
}
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_294 = lean_ctor_get(x_260, 0);
x_295 = lean_ctor_get(x_260, 1);
x_296 = lean_ctor_get_uint8(x_260, sizeof(void*)*4);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_260);
x_297 = lean_ctor_get(x_263, 0);
lean_inc(x_297);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 x_298 = x_263;
} else {
 lean_dec_ref(x_263);
 x_298 = lean_box(0);
}
x_299 = l_Nat_min(x_297, x_2);
lean_dec(x_2);
lean_dec(x_297);
if (lean_is_scalar(x_298)) {
 x_300 = lean_alloc_ctor(1, 1, 0);
} else {
 x_300 = x_298;
}
lean_ctor_set(x_300, 0, x_299);
x_301 = lean_ctor_get(x_15, 2);
lean_inc(x_301);
lean_dec(x_15);
x_302 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_302, 0, x_294);
lean_ctor_set(x_302, 1, x_295);
lean_ctor_set(x_302, 2, x_301);
lean_ctor_set(x_302, 3, x_300);
lean_ctor_set_uint8(x_302, sizeof(void*)*4, x_296);
x_303 = lean_box(0);
lean_ctor_set(x_257, 1, x_302);
lean_ctor_set(x_257, 0, x_303);
if (lean_is_scalar(x_39)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_39;
}
lean_ctor_set(x_304, 0, x_257);
lean_ctor_set(x_304, 1, x_258);
return x_304;
}
}
}
else
{
uint8_t x_305; 
lean_dec(x_2);
x_305 = !lean_is_exclusive(x_260);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_306 = lean_ctor_get(x_260, 3);
lean_dec(x_306);
x_307 = lean_ctor_get(x_260, 2);
lean_dec(x_307);
x_308 = lean_ctor_get(x_15, 3);
lean_inc(x_308);
x_309 = lean_ctor_get(x_15, 2);
lean_inc(x_309);
lean_dec(x_15);
lean_ctor_set(x_260, 3, x_308);
lean_ctor_set(x_260, 2, x_309);
x_310 = lean_box(0);
lean_ctor_set(x_257, 0, x_310);
if (lean_is_scalar(x_39)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_39;
}
lean_ctor_set(x_311, 0, x_257);
lean_ctor_set(x_311, 1, x_258);
return x_311;
}
else
{
lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_312 = lean_ctor_get(x_260, 0);
x_313 = lean_ctor_get(x_260, 1);
x_314 = lean_ctor_get_uint8(x_260, sizeof(void*)*4);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_260);
x_315 = lean_ctor_get(x_15, 3);
lean_inc(x_315);
x_316 = lean_ctor_get(x_15, 2);
lean_inc(x_316);
lean_dec(x_15);
x_317 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_317, 0, x_312);
lean_ctor_set(x_317, 1, x_313);
lean_ctor_set(x_317, 2, x_316);
lean_ctor_set(x_317, 3, x_315);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_314);
x_318 = lean_box(0);
lean_ctor_set(x_257, 1, x_317);
lean_ctor_set(x_257, 0, x_318);
if (lean_is_scalar(x_39)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_39;
}
lean_ctor_set(x_319, 0, x_257);
lean_ctor_set(x_319, 1, x_258);
return x_319;
}
}
}
else
{
lean_object* x_320; uint8_t x_321; 
x_320 = lean_ctor_get(x_257, 1);
lean_inc(x_320);
lean_dec(x_257);
x_321 = lean_ctor_get_uint8(x_15, sizeof(void*)*4);
if (x_321 == 0)
{
lean_object* x_322; 
x_322 = lean_ctor_get(x_320, 3);
lean_inc(x_322);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; uint8_t x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_323 = lean_ctor_get(x_320, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_320, 1);
lean_inc(x_324);
x_325 = lean_ctor_get_uint8(x_320, sizeof(void*)*4);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 lean_ctor_release(x_320, 2);
 lean_ctor_release(x_320, 3);
 x_326 = x_320;
} else {
 lean_dec_ref(x_320);
 x_326 = lean_box(0);
}
x_327 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_327, 0, x_2);
x_328 = lean_ctor_get(x_15, 2);
lean_inc(x_328);
lean_dec(x_15);
if (lean_is_scalar(x_326)) {
 x_329 = lean_alloc_ctor(0, 4, 1);
} else {
 x_329 = x_326;
}
lean_ctor_set(x_329, 0, x_323);
lean_ctor_set(x_329, 1, x_324);
lean_ctor_set(x_329, 2, x_328);
lean_ctor_set(x_329, 3, x_327);
lean_ctor_set_uint8(x_329, sizeof(void*)*4, x_325);
x_330 = lean_box(0);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_329);
if (lean_is_scalar(x_39)) {
 x_332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_332 = x_39;
}
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_258);
return x_332;
}
else
{
lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_333 = lean_ctor_get(x_320, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_320, 1);
lean_inc(x_334);
x_335 = lean_ctor_get_uint8(x_320, sizeof(void*)*4);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 lean_ctor_release(x_320, 2);
 lean_ctor_release(x_320, 3);
 x_336 = x_320;
} else {
 lean_dec_ref(x_320);
 x_336 = lean_box(0);
}
x_337 = lean_ctor_get(x_322, 0);
lean_inc(x_337);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 x_338 = x_322;
} else {
 lean_dec_ref(x_322);
 x_338 = lean_box(0);
}
x_339 = l_Nat_min(x_337, x_2);
lean_dec(x_2);
lean_dec(x_337);
if (lean_is_scalar(x_338)) {
 x_340 = lean_alloc_ctor(1, 1, 0);
} else {
 x_340 = x_338;
}
lean_ctor_set(x_340, 0, x_339);
x_341 = lean_ctor_get(x_15, 2);
lean_inc(x_341);
lean_dec(x_15);
if (lean_is_scalar(x_336)) {
 x_342 = lean_alloc_ctor(0, 4, 1);
} else {
 x_342 = x_336;
}
lean_ctor_set(x_342, 0, x_333);
lean_ctor_set(x_342, 1, x_334);
lean_ctor_set(x_342, 2, x_341);
lean_ctor_set(x_342, 3, x_340);
lean_ctor_set_uint8(x_342, sizeof(void*)*4, x_335);
x_343 = lean_box(0);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_342);
if (lean_is_scalar(x_39)) {
 x_345 = lean_alloc_ctor(0, 2, 0);
} else {
 x_345 = x_39;
}
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_258);
return x_345;
}
}
else
{
lean_object* x_346; lean_object* x_347; uint8_t x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_2);
x_346 = lean_ctor_get(x_320, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_320, 1);
lean_inc(x_347);
x_348 = lean_ctor_get_uint8(x_320, sizeof(void*)*4);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 lean_ctor_release(x_320, 2);
 lean_ctor_release(x_320, 3);
 x_349 = x_320;
} else {
 lean_dec_ref(x_320);
 x_349 = lean_box(0);
}
x_350 = lean_ctor_get(x_15, 3);
lean_inc(x_350);
x_351 = lean_ctor_get(x_15, 2);
lean_inc(x_351);
lean_dec(x_15);
if (lean_is_scalar(x_349)) {
 x_352 = lean_alloc_ctor(0, 4, 1);
} else {
 x_352 = x_349;
}
lean_ctor_set(x_352, 0, x_346);
lean_ctor_set(x_352, 1, x_347);
lean_ctor_set(x_352, 2, x_351);
lean_ctor_set(x_352, 3, x_350);
lean_ctor_set_uint8(x_352, sizeof(void*)*4, x_348);
x_353 = lean_box(0);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_352);
if (lean_is_scalar(x_39)) {
 x_355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_355 = x_39;
}
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_258);
return x_355;
}
}
}
else
{
uint8_t x_356; 
lean_dec(x_39);
x_356 = !lean_is_exclusive(x_257);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; uint8_t x_360; 
x_357 = lean_ctor_get(x_257, 1);
x_358 = lean_ctor_get(x_257, 0);
lean_dec(x_358);
x_359 = lean_unsigned_to_nat(0u);
x_360 = lean_nat_dec_lt(x_359, x_18);
lean_dec(x_18);
if (x_360 == 0)
{
lean_object* x_361; 
x_361 = lean_box(0);
lean_ctor_set(x_257, 0, x_361);
x_186 = x_257;
x_187 = x_258;
goto block_256;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_free_object(x_257);
x_362 = l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___rarg(x_357, x_6, x_258);
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
lean_dec(x_362);
x_186 = x_363;
x_187 = x_364;
goto block_256;
}
}
else
{
lean_object* x_365; lean_object* x_366; uint8_t x_367; 
x_365 = lean_ctor_get(x_257, 1);
lean_inc(x_365);
lean_dec(x_257);
x_366 = lean_unsigned_to_nat(0u);
x_367 = lean_nat_dec_lt(x_366, x_18);
lean_dec(x_18);
if (x_367 == 0)
{
lean_object* x_368; lean_object* x_369; 
x_368 = lean_box(0);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_365);
x_186 = x_369;
x_187 = x_258;
goto block_256;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___rarg(x_365, x_6, x_258);
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_186 = x_371;
x_187 = x_372;
goto block_256;
}
}
}
}
block_409:
{
lean_object* x_376; uint8_t x_377; 
x_376 = lean_ctor_get(x_374, 0);
lean_inc(x_376);
x_377 = lean_unbox(x_376);
lean_dec(x_376);
if (x_377 == 0)
{
uint8_t x_378; 
lean_dec(x_41);
lean_dec(x_40);
x_378 = !lean_is_exclusive(x_374);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_ctor_get(x_374, 0);
lean_dec(x_379);
x_380 = lean_box(0);
lean_ctor_set(x_374, 0, x_380);
x_257 = x_374;
x_258 = x_375;
goto block_373;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_374, 1);
lean_inc(x_381);
lean_dec(x_374);
x_382 = lean_box(0);
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_381);
x_257 = x_383;
x_258 = x_375;
goto block_373;
}
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_384 = lean_ctor_get(x_374, 1);
lean_inc(x_384);
lean_dec(x_374);
lean_inc(x_2);
x_385 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_2);
x_386 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_386, 0, x_385);
x_387 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__17;
x_388 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_386);
x_389 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__20;
x_390 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_390, 0, x_388);
lean_ctor_set(x_390, 1, x_389);
x_391 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_41);
x_392 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_392, 0, x_391);
x_393 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_393, 0, x_390);
lean_ctor_set(x_393, 1, x_392);
x_394 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_395 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
x_396 = l_Lean_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_40);
x_397 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_397, 0, x_396);
x_398 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_397);
x_399 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__23;
x_400 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
x_401 = lean_ctor_get(x_15, 1);
lean_inc(x_401);
x_402 = l_Lean_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_401);
x_403 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_403, 0, x_402);
x_404 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_404, 0, x_400);
lean_ctor_set(x_404, 1, x_403);
x_405 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_406 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_405, x_404, x_4, x_384, x_6, x_375);
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
lean_dec(x_406);
x_257 = x_407;
x_258 = x_408;
goto block_373;
}
}
}
}
}
}
else
{
uint8_t x_428; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_428 = !lean_is_exclusive(x_28);
if (x_428 == 0)
{
return x_28;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_429 = lean_ctor_get(x_28, 0);
x_430 = lean_ctor_get(x_28, 1);
lean_inc(x_430);
lean_inc(x_429);
lean_dec(x_28);
x_431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_431, 0, x_429);
lean_ctor_set(x_431, 1, x_430);
return x_431;
}
}
}
block_474:
{
lean_object* x_435; uint8_t x_436; 
x_435 = lean_ctor_get(x_433, 0);
lean_inc(x_435);
x_436 = lean_unbox(x_435);
lean_dec(x_435);
if (x_436 == 0)
{
uint8_t x_437; 
lean_dec(x_11);
x_437 = !lean_is_exclusive(x_433);
if (x_437 == 0)
{
lean_object* x_438; lean_object* x_439; 
x_438 = lean_ctor_get(x_433, 0);
lean_dec(x_438);
x_439 = lean_box(0);
lean_ctor_set(x_433, 0, x_439);
x_24 = x_433;
x_25 = x_434;
goto block_432;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_433, 1);
lean_inc(x_440);
lean_dec(x_433);
x_441 = lean_box(0);
x_442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_440);
x_24 = x_442;
x_25 = x_434;
goto block_432;
}
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_443 = lean_ctor_get(x_433, 1);
lean_inc(x_443);
lean_dec(x_433);
x_444 = lean_ctor_get(x_15, 1);
lean_inc(x_444);
x_445 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_445, 0, x_11);
x_446 = l_Lean_MessageData_ofList___closed__3;
x_447 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_445);
x_448 = lean_unsigned_to_nat(2u);
x_449 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_447);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_450 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__28;
x_451 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_449);
x_452 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_453 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_452, x_451, x_4, x_443, x_6, x_434);
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
lean_dec(x_453);
x_24 = x_454;
x_25 = x_455;
goto block_432;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_456 = lean_ctor_get(x_444, 0);
lean_inc(x_456);
lean_dec(x_444);
x_457 = l_Nat_repr(x_456);
x_458 = l_addParenHeuristic(x_457);
lean_dec(x_457);
x_459 = l_Option_HasRepr___rarg___closed__2;
x_460 = lean_string_append(x_459, x_458);
lean_dec(x_458);
x_461 = l_Option_HasRepr___rarg___closed__3;
x_462 = lean_string_append(x_460, x_461);
x_463 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_463, 0, x_462);
x_464 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_464, 0, x_463);
x_465 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__26;
x_466 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_464);
x_467 = l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__4;
x_468 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_468, 0, x_466);
lean_ctor_set(x_468, 1, x_467);
x_469 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_469, 0, x_468);
lean_ctor_set(x_469, 1, x_449);
x_470 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_471 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_470, x_469, x_4, x_443, x_6, x_434);
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_471, 1);
lean_inc(x_473);
lean_dec(x_471);
x_24 = x_472;
x_25 = x_473;
goto block_432;
}
}
}
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_721; lean_object* x_722; lean_object* x_761; uint8_t x_762; 
x_482 = lean_ctor_get(x_14, 0);
lean_inc(x_482);
lean_dec(x_14);
x_483 = lean_ctor_get(x_15, 0);
lean_inc(x_483);
x_484 = lean_box(0);
x_485 = 0;
x_486 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_484);
lean_ctor_set(x_486, 2, x_484);
lean_ctor_set(x_486, 3, x_484);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_485);
x_761 = lean_ctor_get(x_16, 4);
lean_inc(x_761);
x_762 = lean_ctor_get_uint8(x_761, sizeof(void*)*1);
lean_dec(x_761);
if (x_762 == 0)
{
lean_object* x_763; lean_object* x_764; 
x_763 = lean_box(x_485);
x_764 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_764, 0, x_763);
lean_ctor_set(x_764, 1, x_486);
x_721 = x_764;
x_722 = x_16;
goto block_760;
}
else
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
x_765 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_766 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_765, x_6, x_16);
x_767 = lean_ctor_get(x_766, 0);
lean_inc(x_767);
x_768 = lean_ctor_get(x_766, 1);
lean_inc(x_768);
lean_dec(x_766);
x_769 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_769, 0, x_767);
lean_ctor_set(x_769, 1, x_486);
x_721 = x_769;
x_722 = x_768;
goto block_760;
}
block_720:
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_489 = lean_ctor_get(x_487, 1);
lean_inc(x_489);
lean_dec(x_487);
lean_inc(x_1);
x_490 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_490, 0, x_1);
lean_inc(x_6);
x_491 = lean_apply_4(x_3, x_490, x_489, x_6, x_488);
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_492, 1);
lean_inc(x_493);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 x_494 = x_492;
} else {
 lean_dec_ref(x_492);
 x_494 = lean_box(0);
}
x_495 = lean_ctor_get(x_493, 2);
lean_inc(x_495);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_494);
lean_dec(x_482);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_496 = lean_ctor_get(x_491, 1);
lean_inc(x_496);
lean_dec(x_491);
x_497 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__6;
x_498 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__9;
x_499 = lean_panic_fn(x_497, x_498);
x_500 = lean_apply_4(x_499, x_4, x_493, x_6, x_496);
return x_500;
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; uint8_t x_710; 
x_501 = lean_ctor_get(x_491, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_502 = x_491;
} else {
 lean_dec_ref(x_491);
 x_502 = lean_box(0);
}
x_503 = lean_ctor_get(x_493, 3);
lean_inc(x_503);
x_504 = lean_ctor_get(x_495, 0);
lean_inc(x_504);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 x_505 = x_495;
} else {
 lean_dec_ref(x_495);
 x_505 = lean_box(0);
}
x_710 = lean_nat_dec_lt(x_504, x_2);
if (x_710 == 0)
{
if (lean_obj_tag(x_503) == 0)
{
x_506 = x_710;
goto block_709;
}
else
{
lean_object* x_711; 
x_711 = lean_ctor_get(x_15, 1);
lean_inc(x_711);
if (lean_obj_tag(x_711) == 0)
{
x_506 = x_710;
goto block_709;
}
else
{
lean_object* x_712; lean_object* x_713; uint8_t x_714; 
x_712 = lean_ctor_get(x_503, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_711, 0);
lean_inc(x_713);
lean_dec(x_711);
x_714 = lean_nat_dec_le(x_712, x_713);
lean_dec(x_713);
lean_dec(x_712);
x_506 = x_714;
goto block_709;
}
}
}
else
{
uint8_t x_715; 
x_715 = 1;
x_506 = x_715;
goto block_709;
}
block_709:
{
uint8_t x_507; 
if (x_506 == 0)
{
x_507 = x_485;
goto block_707;
}
else
{
uint8_t x_708; 
x_708 = 1;
x_507 = x_708;
goto block_707;
}
block_707:
{
lean_object* x_508; lean_object* x_509; lean_object* x_541; lean_object* x_542; lean_object* x_573; lean_object* x_574; lean_object* x_615; lean_object* x_616; lean_object* x_664; lean_object* x_665; lean_object* x_698; uint8_t x_699; 
x_698 = lean_ctor_get(x_501, 4);
lean_inc(x_698);
x_699 = lean_ctor_get_uint8(x_698, sizeof(void*)*1);
lean_dec(x_698);
if (x_699 == 0)
{
lean_object* x_700; lean_object* x_701; 
x_700 = lean_box(x_485);
if (lean_is_scalar(x_494)) {
 x_701 = lean_alloc_ctor(0, 2, 0);
} else {
 x_701 = x_494;
}
lean_ctor_set(x_701, 0, x_700);
lean_ctor_set(x_701, 1, x_493);
x_664 = x_701;
x_665 = x_501;
goto block_697;
}
else
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_702 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_703 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_702, x_6, x_501);
x_704 = lean_ctor_get(x_703, 0);
lean_inc(x_704);
x_705 = lean_ctor_get(x_703, 1);
lean_inc(x_705);
lean_dec(x_703);
if (lean_is_scalar(x_494)) {
 x_706 = lean_alloc_ctor(0, 2, 0);
} else {
 x_706 = x_494;
}
lean_ctor_set(x_706, 0, x_704);
lean_ctor_set(x_706, 1, x_493);
x_664 = x_706;
x_665 = x_705;
goto block_697;
}
block_540:
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; uint8_t x_515; 
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec(x_508);
x_511 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__2___rarg(x_510, x_6, x_509);
lean_dec(x_6);
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_512, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_512)) {
 lean_ctor_release(x_512, 0);
 lean_ctor_release(x_512, 1);
 x_514 = x_512;
} else {
 lean_dec_ref(x_512);
 x_514 = lean_box(0);
}
x_515 = lean_ctor_get_uint8(x_15, sizeof(void*)*4);
if (x_515 == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; uint8_t x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_516 = lean_ctor_get(x_511, 1);
lean_inc(x_516);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_517 = x_511;
} else {
 lean_dec_ref(x_511);
 x_517 = lean_box(0);
}
x_518 = lean_ctor_get(x_513, 0);
lean_inc(x_518);
x_519 = lean_ctor_get_uint8(x_513, sizeof(void*)*4);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 lean_ctor_release(x_513, 2);
 lean_ctor_release(x_513, 3);
 x_520 = x_513;
} else {
 lean_dec_ref(x_513);
 x_520 = lean_box(0);
}
if (lean_is_scalar(x_505)) {
 x_521 = lean_alloc_ctor(1, 1, 0);
} else {
 x_521 = x_505;
}
lean_ctor_set(x_521, 0, x_2);
x_522 = lean_ctor_get(x_15, 2);
lean_inc(x_522);
lean_dec(x_15);
x_523 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
if (lean_is_scalar(x_520)) {
 x_524 = lean_alloc_ctor(0, 4, 1);
} else {
 x_524 = x_520;
}
lean_ctor_set(x_524, 0, x_518);
lean_ctor_set(x_524, 1, x_523);
lean_ctor_set(x_524, 2, x_522);
lean_ctor_set(x_524, 3, x_521);
lean_ctor_set_uint8(x_524, sizeof(void*)*4, x_519);
x_525 = lean_box(0);
if (lean_is_scalar(x_514)) {
 x_526 = lean_alloc_ctor(0, 2, 0);
} else {
 x_526 = x_514;
}
lean_ctor_set(x_526, 0, x_525);
lean_ctor_set(x_526, 1, x_524);
if (lean_is_scalar(x_517)) {
 x_527 = lean_alloc_ctor(0, 2, 0);
} else {
 x_527 = x_517;
}
lean_ctor_set(x_527, 0, x_526);
lean_ctor_set(x_527, 1, x_516);
return x_527;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; uint8_t x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_505);
lean_dec(x_2);
x_528 = lean_ctor_get(x_511, 1);
lean_inc(x_528);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_529 = x_511;
} else {
 lean_dec_ref(x_511);
 x_529 = lean_box(0);
}
x_530 = lean_ctor_get(x_513, 0);
lean_inc(x_530);
x_531 = lean_ctor_get_uint8(x_513, sizeof(void*)*4);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 lean_ctor_release(x_513, 2);
 lean_ctor_release(x_513, 3);
 x_532 = x_513;
} else {
 lean_dec_ref(x_513);
 x_532 = lean_box(0);
}
x_533 = lean_ctor_get(x_15, 3);
lean_inc(x_533);
x_534 = lean_ctor_get(x_15, 2);
lean_inc(x_534);
lean_dec(x_15);
x_535 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__10;
if (lean_is_scalar(x_532)) {
 x_536 = lean_alloc_ctor(0, 4, 1);
} else {
 x_536 = x_532;
}
lean_ctor_set(x_536, 0, x_530);
lean_ctor_set(x_536, 1, x_535);
lean_ctor_set(x_536, 2, x_534);
lean_ctor_set(x_536, 3, x_533);
lean_ctor_set_uint8(x_536, sizeof(void*)*4, x_531);
x_537 = lean_box(0);
if (lean_is_scalar(x_514)) {
 x_538 = lean_alloc_ctor(0, 2, 0);
} else {
 x_538 = x_514;
}
lean_ctor_set(x_538, 0, x_537);
lean_ctor_set(x_538, 1, x_536);
if (lean_is_scalar(x_529)) {
 x_539 = lean_alloc_ctor(0, 2, 0);
} else {
 x_539 = x_529;
}
lean_ctor_set(x_539, 0, x_538);
lean_ctor_set(x_539, 1, x_528);
return x_539;
}
}
block_572:
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; uint8_t x_548; 
x_543 = lean_ctor_get(x_541, 1);
lean_inc(x_543);
lean_dec(x_541);
x_544 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_543, x_6, x_542);
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_544, 1);
lean_inc(x_546);
lean_dec(x_544);
x_547 = lean_ctor_get(x_546, 4);
lean_inc(x_547);
x_548 = lean_ctor_get_uint8(x_547, sizeof(void*)*1);
lean_dec(x_547);
if (x_548 == 0)
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_4);
x_549 = lean_ctor_get(x_545, 1);
lean_inc(x_549);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 lean_ctor_release(x_545, 1);
 x_550 = x_545;
} else {
 lean_dec_ref(x_545);
 x_550 = lean_box(0);
}
x_551 = lean_box(0);
if (lean_is_scalar(x_550)) {
 x_552 = lean_alloc_ctor(0, 2, 0);
} else {
 x_552 = x_550;
}
lean_ctor_set(x_552, 0, x_551);
lean_ctor_set(x_552, 1, x_549);
x_508 = x_552;
x_509 = x_546;
goto block_540;
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; 
x_553 = lean_ctor_get(x_545, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_545, 1);
lean_inc(x_554);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 lean_ctor_release(x_545, 1);
 x_555 = x_545;
} else {
 lean_dec_ref(x_545);
 x_555 = lean_box(0);
}
x_556 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_557 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_556, x_6, x_546);
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_unbox(x_558);
lean_dec(x_558);
if (x_559 == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; 
lean_dec(x_553);
lean_dec(x_4);
x_560 = lean_ctor_get(x_557, 1);
lean_inc(x_560);
lean_dec(x_557);
x_561 = lean_box(0);
if (lean_is_scalar(x_555)) {
 x_562 = lean_alloc_ctor(0, 2, 0);
} else {
 x_562 = x_555;
}
lean_ctor_set(x_562, 0, x_561);
lean_ctor_set(x_562, 1, x_554);
x_508 = x_562;
x_509 = x_560;
goto block_540;
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
lean_dec(x_555);
x_563 = lean_ctor_get(x_557, 1);
lean_inc(x_563);
lean_dec(x_557);
x_564 = lean_unsigned_to_nat(0u);
x_565 = l_Lean_Syntax_formatStxAux___main(x_484, x_485, x_564, x_553);
x_566 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_566, 0, x_565);
x_567 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__13;
x_568 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_568, 0, x_567);
lean_ctor_set(x_568, 1, x_566);
x_569 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_556, x_568, x_4, x_554, x_6, x_563);
lean_dec(x_4);
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_569, 1);
lean_inc(x_571);
lean_dec(x_569);
x_508 = x_570;
x_509 = x_571;
goto block_540;
}
}
}
block_614:
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
lean_dec(x_573);
x_576 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Parenthesizer_visitArgs___spec__1___rarg(x_575, x_6, x_574);
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
lean_dec(x_576);
x_579 = lean_ctor_get(x_577, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_577, 1);
lean_inc(x_580);
lean_dec(x_577);
x_581 = l_Lean_Syntax_getHeadInfo___main(x_579);
if (lean_obj_tag(x_581) == 0)
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_582 = lean_apply_1(x_1, x_579);
x_583 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_582, x_4, x_580, x_6, x_578);
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_583, 1);
lean_inc(x_585);
lean_dec(x_583);
x_541 = x_584;
x_542 = x_585;
goto block_572;
}
else
{
lean_object* x_586; lean_object* x_587; 
x_586 = lean_ctor_get(x_581, 0);
lean_inc(x_586);
lean_dec(x_581);
x_587 = l_Lean_Syntax_getTailInfo___main(x_579);
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
lean_dec(x_586);
x_588 = lean_apply_1(x_1, x_579);
x_589 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_588, x_4, x_580, x_6, x_578);
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_589, 1);
lean_inc(x_591);
lean_dec(x_589);
x_541 = x_590;
x_542 = x_591;
goto block_572;
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_592 = lean_ctor_get(x_587, 0);
lean_inc(x_592);
lean_dec(x_587);
x_593 = lean_ctor_get(x_586, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_586, 1);
lean_inc(x_594);
x_595 = lean_ctor_get(x_586, 2);
lean_inc(x_595);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 lean_ctor_release(x_586, 2);
 x_596 = x_586;
} else {
 lean_dec_ref(x_586);
 x_596 = lean_box(0);
}
x_597 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__14;
lean_inc(x_594);
if (lean_is_scalar(x_596)) {
 x_598 = lean_alloc_ctor(0, 3, 0);
} else {
 x_598 = x_596;
}
lean_ctor_set(x_598, 0, x_597);
lean_ctor_set(x_598, 1, x_594);
lean_ctor_set(x_598, 2, x_595);
x_599 = l_Lean_Syntax_setHeadInfo(x_579, x_598);
x_600 = lean_ctor_get(x_592, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_592, 1);
lean_inc(x_601);
x_602 = lean_ctor_get(x_592, 2);
lean_inc(x_602);
if (lean_is_exclusive(x_592)) {
 lean_ctor_release(x_592, 0);
 lean_ctor_release(x_592, 1);
 lean_ctor_release(x_592, 2);
 x_603 = x_592;
} else {
 lean_dec_ref(x_592);
 x_603 = lean_box(0);
}
lean_inc(x_601);
if (lean_is_scalar(x_603)) {
 x_604 = lean_alloc_ctor(0, 3, 0);
} else {
 x_604 = x_603;
}
lean_ctor_set(x_604, 0, x_600);
lean_ctor_set(x_604, 1, x_601);
lean_ctor_set(x_604, 2, x_597);
x_605 = l_Lean_Syntax_setTailInfo(x_599, x_604);
x_606 = lean_apply_1(x_1, x_605);
x_607 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_607, 0, x_593);
lean_ctor_set(x_607, 1, x_594);
lean_ctor_set(x_607, 2, x_597);
x_608 = l_Lean_Syntax_setHeadInfo(x_606, x_607);
x_609 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_609, 0, x_597);
lean_ctor_set(x_609, 1, x_601);
lean_ctor_set(x_609, 2, x_602);
x_610 = l_Lean_Syntax_setTailInfo(x_608, x_609);
x_611 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_610, x_4, x_580, x_6, x_578);
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_611, 1);
lean_inc(x_613);
lean_dec(x_611);
x_541 = x_612;
x_542 = x_613;
goto block_572;
}
}
}
block_663:
{
if (x_507 == 0)
{
lean_object* x_617; lean_object* x_618; uint8_t x_619; 
lean_dec(x_505);
lean_dec(x_482);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_617 = lean_ctor_get(x_615, 1);
lean_inc(x_617);
if (lean_is_exclusive(x_615)) {
 lean_ctor_release(x_615, 0);
 lean_ctor_release(x_615, 1);
 x_618 = x_615;
} else {
 lean_dec_ref(x_615);
 x_618 = lean_box(0);
}
x_619 = lean_ctor_get_uint8(x_15, sizeof(void*)*4);
if (x_619 == 0)
{
lean_object* x_620; 
x_620 = lean_ctor_get(x_617, 3);
lean_inc(x_620);
if (lean_obj_tag(x_620) == 0)
{
lean_object* x_621; lean_object* x_622; uint8_t x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_621 = lean_ctor_get(x_617, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_617, 1);
lean_inc(x_622);
x_623 = lean_ctor_get_uint8(x_617, sizeof(void*)*4);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 lean_ctor_release(x_617, 2);
 lean_ctor_release(x_617, 3);
 x_624 = x_617;
} else {
 lean_dec_ref(x_617);
 x_624 = lean_box(0);
}
x_625 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_625, 0, x_2);
x_626 = lean_ctor_get(x_15, 2);
lean_inc(x_626);
lean_dec(x_15);
if (lean_is_scalar(x_624)) {
 x_627 = lean_alloc_ctor(0, 4, 1);
} else {
 x_627 = x_624;
}
lean_ctor_set(x_627, 0, x_621);
lean_ctor_set(x_627, 1, x_622);
lean_ctor_set(x_627, 2, x_626);
lean_ctor_set(x_627, 3, x_625);
lean_ctor_set_uint8(x_627, sizeof(void*)*4, x_623);
x_628 = lean_box(0);
if (lean_is_scalar(x_618)) {
 x_629 = lean_alloc_ctor(0, 2, 0);
} else {
 x_629 = x_618;
}
lean_ctor_set(x_629, 0, x_628);
lean_ctor_set(x_629, 1, x_627);
if (lean_is_scalar(x_502)) {
 x_630 = lean_alloc_ctor(0, 2, 0);
} else {
 x_630 = x_502;
}
lean_ctor_set(x_630, 0, x_629);
lean_ctor_set(x_630, 1, x_616);
return x_630;
}
else
{
lean_object* x_631; lean_object* x_632; uint8_t x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_631 = lean_ctor_get(x_617, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_617, 1);
lean_inc(x_632);
x_633 = lean_ctor_get_uint8(x_617, sizeof(void*)*4);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 lean_ctor_release(x_617, 2);
 lean_ctor_release(x_617, 3);
 x_634 = x_617;
} else {
 lean_dec_ref(x_617);
 x_634 = lean_box(0);
}
x_635 = lean_ctor_get(x_620, 0);
lean_inc(x_635);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 x_636 = x_620;
} else {
 lean_dec_ref(x_620);
 x_636 = lean_box(0);
}
x_637 = l_Nat_min(x_635, x_2);
lean_dec(x_2);
lean_dec(x_635);
if (lean_is_scalar(x_636)) {
 x_638 = lean_alloc_ctor(1, 1, 0);
} else {
 x_638 = x_636;
}
lean_ctor_set(x_638, 0, x_637);
x_639 = lean_ctor_get(x_15, 2);
lean_inc(x_639);
lean_dec(x_15);
if (lean_is_scalar(x_634)) {
 x_640 = lean_alloc_ctor(0, 4, 1);
} else {
 x_640 = x_634;
}
lean_ctor_set(x_640, 0, x_631);
lean_ctor_set(x_640, 1, x_632);
lean_ctor_set(x_640, 2, x_639);
lean_ctor_set(x_640, 3, x_638);
lean_ctor_set_uint8(x_640, sizeof(void*)*4, x_633);
x_641 = lean_box(0);
if (lean_is_scalar(x_618)) {
 x_642 = lean_alloc_ctor(0, 2, 0);
} else {
 x_642 = x_618;
}
lean_ctor_set(x_642, 0, x_641);
lean_ctor_set(x_642, 1, x_640);
if (lean_is_scalar(x_502)) {
 x_643 = lean_alloc_ctor(0, 2, 0);
} else {
 x_643 = x_502;
}
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_616);
return x_643;
}
}
else
{
lean_object* x_644; lean_object* x_645; uint8_t x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_2);
x_644 = lean_ctor_get(x_617, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_617, 1);
lean_inc(x_645);
x_646 = lean_ctor_get_uint8(x_617, sizeof(void*)*4);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 lean_ctor_release(x_617, 2);
 lean_ctor_release(x_617, 3);
 x_647 = x_617;
} else {
 lean_dec_ref(x_617);
 x_647 = lean_box(0);
}
x_648 = lean_ctor_get(x_15, 3);
lean_inc(x_648);
x_649 = lean_ctor_get(x_15, 2);
lean_inc(x_649);
lean_dec(x_15);
if (lean_is_scalar(x_647)) {
 x_650 = lean_alloc_ctor(0, 4, 1);
} else {
 x_650 = x_647;
}
lean_ctor_set(x_650, 0, x_644);
lean_ctor_set(x_650, 1, x_645);
lean_ctor_set(x_650, 2, x_649);
lean_ctor_set(x_650, 3, x_648);
lean_ctor_set_uint8(x_650, sizeof(void*)*4, x_646);
x_651 = lean_box(0);
if (lean_is_scalar(x_618)) {
 x_652 = lean_alloc_ctor(0, 2, 0);
} else {
 x_652 = x_618;
}
lean_ctor_set(x_652, 0, x_651);
lean_ctor_set(x_652, 1, x_650);
if (lean_is_scalar(x_502)) {
 x_653 = lean_alloc_ctor(0, 2, 0);
} else {
 x_653 = x_502;
}
lean_ctor_set(x_653, 0, x_652);
lean_ctor_set(x_653, 1, x_616);
return x_653;
}
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; uint8_t x_657; 
lean_dec(x_502);
x_654 = lean_ctor_get(x_615, 1);
lean_inc(x_654);
if (lean_is_exclusive(x_615)) {
 lean_ctor_release(x_615, 0);
 lean_ctor_release(x_615, 1);
 x_655 = x_615;
} else {
 lean_dec_ref(x_615);
 x_655 = lean_box(0);
}
x_656 = lean_unsigned_to_nat(0u);
x_657 = lean_nat_dec_lt(x_656, x_482);
lean_dec(x_482);
if (x_657 == 0)
{
lean_object* x_658; lean_object* x_659; 
x_658 = lean_box(0);
if (lean_is_scalar(x_655)) {
 x_659 = lean_alloc_ctor(0, 2, 0);
} else {
 x_659 = x_655;
}
lean_ctor_set(x_659, 0, x_658);
lean_ctor_set(x_659, 1, x_654);
x_573 = x_659;
x_574 = x_616;
goto block_614;
}
else
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; 
lean_dec(x_655);
x_660 = l_Lean_Syntax_MonadTraverser_goRight___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__4___rarg(x_654, x_6, x_616);
x_661 = lean_ctor_get(x_660, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_660, 1);
lean_inc(x_662);
lean_dec(x_660);
x_573 = x_661;
x_574 = x_662;
goto block_614;
}
}
}
block_697:
{
lean_object* x_666; uint8_t x_667; 
x_666 = lean_ctor_get(x_664, 0);
lean_inc(x_666);
x_667 = lean_unbox(x_666);
lean_dec(x_666);
if (x_667 == 0)
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; 
lean_dec(x_504);
lean_dec(x_503);
x_668 = lean_ctor_get(x_664, 1);
lean_inc(x_668);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 lean_ctor_release(x_664, 1);
 x_669 = x_664;
} else {
 lean_dec_ref(x_664);
 x_669 = lean_box(0);
}
x_670 = lean_box(0);
if (lean_is_scalar(x_669)) {
 x_671 = lean_alloc_ctor(0, 2, 0);
} else {
 x_671 = x_669;
}
lean_ctor_set(x_671, 0, x_670);
lean_ctor_set(x_671, 1, x_668);
x_615 = x_671;
x_616 = x_665;
goto block_663;
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_672 = lean_ctor_get(x_664, 1);
lean_inc(x_672);
lean_dec(x_664);
lean_inc(x_2);
x_673 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_2);
x_674 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_674, 0, x_673);
x_675 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__17;
x_676 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_676, 0, x_675);
lean_ctor_set(x_676, 1, x_674);
x_677 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__20;
x_678 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_678, 0, x_676);
lean_ctor_set(x_678, 1, x_677);
x_679 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_504);
x_680 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_680, 0, x_679);
x_681 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_681, 0, x_678);
lean_ctor_set(x_681, 1, x_680);
x_682 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_683 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_683, 0, x_681);
lean_ctor_set(x_683, 1, x_682);
x_684 = l_Lean_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_503);
x_685 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_685, 0, x_684);
x_686 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_686, 0, x_683);
lean_ctor_set(x_686, 1, x_685);
x_687 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__23;
x_688 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_688, 0, x_686);
lean_ctor_set(x_688, 1, x_687);
x_689 = lean_ctor_get(x_15, 1);
lean_inc(x_689);
x_690 = l_Lean_Option_format___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__6(x_689);
x_691 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_691, 0, x_690);
x_692 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_692, 0, x_688);
lean_ctor_set(x_692, 1, x_691);
x_693 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_694 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_693, x_692, x_4, x_672, x_6, x_665);
x_695 = lean_ctor_get(x_694, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_694, 1);
lean_inc(x_696);
lean_dec(x_694);
x_615 = x_695;
x_616 = x_696;
goto block_663;
}
}
}
}
}
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
lean_dec(x_482);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_716 = lean_ctor_get(x_491, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_491, 1);
lean_inc(x_717);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_718 = x_491;
} else {
 lean_dec_ref(x_491);
 x_718 = lean_box(0);
}
if (lean_is_scalar(x_718)) {
 x_719 = lean_alloc_ctor(1, 2, 0);
} else {
 x_719 = x_718;
}
lean_ctor_set(x_719, 0, x_716);
lean_ctor_set(x_719, 1, x_717);
return x_719;
}
}
block_760:
{
lean_object* x_723; uint8_t x_724; 
x_723 = lean_ctor_get(x_721, 0);
lean_inc(x_723);
x_724 = lean_unbox(x_723);
lean_dec(x_723);
if (x_724 == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
lean_dec(x_11);
x_725 = lean_ctor_get(x_721, 1);
lean_inc(x_725);
if (lean_is_exclusive(x_721)) {
 lean_ctor_release(x_721, 0);
 lean_ctor_release(x_721, 1);
 x_726 = x_721;
} else {
 lean_dec_ref(x_721);
 x_726 = lean_box(0);
}
x_727 = lean_box(0);
if (lean_is_scalar(x_726)) {
 x_728 = lean_alloc_ctor(0, 2, 0);
} else {
 x_728 = x_726;
}
lean_ctor_set(x_728, 0, x_727);
lean_ctor_set(x_728, 1, x_725);
x_487 = x_728;
x_488 = x_722;
goto block_720;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
x_729 = lean_ctor_get(x_721, 1);
lean_inc(x_729);
lean_dec(x_721);
x_730 = lean_ctor_get(x_15, 1);
lean_inc(x_730);
x_731 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_731, 0, x_11);
x_732 = l_Lean_MessageData_ofList___closed__3;
x_733 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_733, 0, x_732);
lean_ctor_set(x_733, 1, x_731);
x_734 = lean_unsigned_to_nat(2u);
x_735 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set(x_735, 1, x_733);
if (lean_obj_tag(x_730) == 0)
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; 
x_736 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__28;
x_737 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_737, 0, x_736);
lean_ctor_set(x_737, 1, x_735);
x_738 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_739 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_738, x_737, x_4, x_729, x_6, x_722);
x_740 = lean_ctor_get(x_739, 0);
lean_inc(x_740);
x_741 = lean_ctor_get(x_739, 1);
lean_inc(x_741);
lean_dec(x_739);
x_487 = x_740;
x_488 = x_741;
goto block_720;
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; 
x_742 = lean_ctor_get(x_730, 0);
lean_inc(x_742);
lean_dec(x_730);
x_743 = l_Nat_repr(x_742);
x_744 = l_addParenHeuristic(x_743);
lean_dec(x_743);
x_745 = l_Option_HasRepr___rarg___closed__2;
x_746 = lean_string_append(x_745, x_744);
lean_dec(x_744);
x_747 = l_Option_HasRepr___rarg___closed__3;
x_748 = lean_string_append(x_746, x_747);
x_749 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_749, 0, x_748);
x_750 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_750, 0, x_749);
x_751 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__26;
x_752 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_752, 0, x_751);
lean_ctor_set(x_752, 1, x_750);
x_753 = l_Lean_Meta_DepElim_Pattern_toMessageData___main___closed__4;
x_754 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_754, 0, x_752);
lean_ctor_set(x_754, 1, x_753);
x_755 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_755, 0, x_754);
lean_ctor_set(x_755, 1, x_735);
x_756 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_757 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_756, x_755, x_4, x_729, x_6, x_722);
x_758 = lean_ctor_get(x_757, 0);
lean_inc(x_758);
x_759 = lean_ctor_get(x_757, 1);
lean_inc(x_759);
lean_dec(x_757);
x_487 = x_758;
x_488 = x_759;
goto block_720;
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
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_MonadTraverser_setCur___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___rarg___boxed), 3, 0);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27(x_1, x_2, x_5, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
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
x_15 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
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
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed), 4, 3);
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
x_25 = lean_alloc_closure((void*)(l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___spec__1___boxed), 6, 2);
lean_closure_set(x_25, 0, x_24);
lean_closure_set(x_25, 1, x_24);
x_26 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_25, x_3, x_11, x_5, x_9);
return x_26;
}
}
}
lean_object* l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forMAux___main___at_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
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
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___spec__1___rarg), 4, 0);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("paren");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__3() {
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
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__5() {
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
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__6() {
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = l_Array_empty___closed__1;
x_6 = lean_array_push(x_5, x_1);
x_7 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__5;
x_8 = lean_array_push(x_6, x_7);
x_9 = l_Lean_nullKind___closed__2;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__4;
x_12 = lean_array_push(x_11, x_10);
x_13 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__6;
x_14 = lean_array_push(x_12, x_13);
x_15 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__2;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Unhygienic_MonadQuotation___closed__4;
x_4 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___spec__1___rarg), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Lean_Unhygienic_run___rarg(x_4);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("term");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__2), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__5;
x_3 = lean_alloc_ctor(22, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_15 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__2;
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___boxed), 6, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_1);
x_17 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__3;
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
x_19 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__6;
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
x_27 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__2;
lean_inc(x_1);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___boxed), 6, 2);
lean_closure_set(x_28, 0, x_27);
lean_closure_set(x_28, 1, x_1);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__3;
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
x_31 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__6;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_21);
return x_32;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__1;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("seq");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__1;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__4;
x_13 = lean_array_push(x_12, x_11);
x_14 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__6;
x_15 = lean_array_push(x_13, x_14);
x_16 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__2;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Unhygienic_MonadQuotation___closed__4;
x_4 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___spec__1___rarg), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Lean_Unhygienic_run___rarg(x_4);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tactic");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__2), 1, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___closed__2;
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___boxed), 6, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
x_8 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___closed__3;
x_9 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_8, x_1, x_7, x_2, x_3, x_4, x_5);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Level");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___closed__2;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__4;
x_6 = lean_array_push(x_5, x_1);
x_7 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__6;
x_8 = lean_array_push(x_6, x_7);
x_9 = l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___closed__3;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Unhygienic_MonadQuotation___closed__4;
x_4 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___spec__1___rarg), 4, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Lean_Unhygienic_run___rarg(x_4);
return x_5;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("level");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__2), 1, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___closed__2;
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___boxed), 6, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
x_8 = l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___closed__3;
x_9 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_8, x_1, x_7, x_2, x_3, x_4, x_5);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_62; 
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
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_13 = x_8;
} else {
 lean_dec_ref(x_8);
 x_13 = lean_box(0);
}
x_14 = l_Lean_Syntax_getKind(x_11);
x_62 = lean_name_eq(x_1, x_14);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = 1;
x_15 = x_63;
goto block_61;
}
else
{
uint8_t x_64; 
x_64 = 0;
x_15 = x_64;
goto block_61;
}
block_61:
{
uint8_t x_16; 
if (x_15 == 0)
{
uint8_t x_59; 
x_59 = 0;
x_16 = x_59;
goto block_58;
}
else
{
uint8_t x_60; 
x_60 = 1;
x_16 = x_60;
goto block_58;
}
block_58:
{
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_1);
x_17 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_2, x_3, x_12, x_5, x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_48; uint8_t x_49; 
lean_dec(x_2);
x_48 = lean_ctor_get(x_9, 4);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*1);
lean_dec(x_48);
if (x_49 == 0)
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_50 = 0;
x_51 = lean_box(x_50);
if (lean_is_scalar(x_13)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_13;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_12);
x_18 = x_52;
x_19 = x_9;
goto block_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_54 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_53, x_5, x_9);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
if (lean_is_scalar(x_13)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_13;
}
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_12);
x_18 = x_57;
x_19 = x_56;
goto block_47;
}
block_47:
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_22 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__6;
if (lean_is_scalar(x_10)) {
 x_23 = lean_alloc_ctor(1, 2, 0);
} else {
 x_23 = x_10;
 lean_ctor_set_tag(x_23, 1);
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_10);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = l_Lean_Name_toString___closed__1;
x_26 = l_Lean_Name_toStringWithSep___main(x_25, x_14);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__5;
x_30 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__8;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Name_toStringWithSep___main(x_25, x_1);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
x_37 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_38 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_40 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_39, x_38, x_3, x_24, x_5, x_19);
lean_dec(x_5);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__6;
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__6;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
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
x_1 = lean_unsigned_to_nat(1023u);
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
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trailingNode.parenthesizer called outside of visitParenthesizable call");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__7;
x_2 = lean_unsigned_to_nat(316u);
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
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___boxed), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_4);
x_8 = lean_apply_4(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck(x_2, x_4, x_11, x_6, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_PUnit_Inhabited;
x_17 = l_monadInhabited___rarg(x_3, x_16);
x_18 = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__2;
x_19 = lean_panic_fn(x_17, x_18);
x_20 = lean_apply_4(x_19, x_4, x_15, x_6, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_3);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1___closed__5;
x_26 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize(x_23, x_24, x_25, x_4, x_22, x_6, x_21);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
return x_8;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_8);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
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
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_14 = x_9;
} else {
 lean_dec_ref(x_9);
 x_14 = lean_box(0);
}
x_15 = l_Lean_Syntax_getKind(x_12);
x_16 = lean_name_eq(x_1, x_15);
x_17 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__2;
x_18 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___lambda__1), 7, 3);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_17);
if (x_16 == 0)
{
uint8_t x_66; 
x_66 = 1;
x_19 = x_66;
goto block_65;
}
else
{
uint8_t x_67; 
x_67 = 0;
x_19 = x_67;
goto block_65;
}
block_65:
{
uint8_t x_20; 
if (x_19 == 0)
{
uint8_t x_63; 
x_63 = 0;
x_20 = x_63;
goto block_62;
}
else
{
uint8_t x_64; 
x_64 = 1;
x_20 = x_64;
goto block_62;
}
block_62:
{
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_1);
x_21 = l_Lean_PrettyPrinter_Parenthesizer_visitArgs(x_18, x_4, x_13, x_6, x_10);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_52; uint8_t x_53; 
lean_dec(x_18);
x_52 = lean_ctor_get(x_10, 4);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_52, sizeof(void*)*1);
lean_dec(x_52);
if (x_53 == 0)
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_54 = 0;
x_55 = lean_box(x_54);
if (lean_is_scalar(x_14)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_14;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_13);
x_22 = x_56;
x_23 = x_10;
goto block_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_58 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_57, x_6, x_10);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
if (lean_is_scalar(x_14)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_14;
}
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_13);
x_22 = x_61;
x_23 = x_60;
goto block_51;
}
block_51:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_26 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__6;
if (lean_is_scalar(x_11)) {
 x_27 = lean_alloc_ctor(1, 2, 0);
} else {
 x_27 = x_11;
 lean_ctor_set_tag(x_27, 1);
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_11);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = l_Lean_Name_toString___closed__1;
x_30 = l_Lean_Name_toStringWithSep___main(x_29, x_15);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__5;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__8;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Name_toStringWithSep___main(x_29, x_1);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
x_41 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__2;
x_44 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___spec__2(x_43, x_42, x_4, x_28, x_6, x_23);
lean_dec(x_6);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
x_47 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__6;
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__6;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
}
}
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
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
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
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
uint8_t x_7; 
x_7 = l_Lean_Expr_isConstOf(x_4, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_6);
return x_9;
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
x_22 = l_Lean_Meta_mkAuxName___closed__1;
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
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
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
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_22 = l_Lean_Meta_mkAuxName___closed__1;
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
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
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
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_22 = l_Lean_Meta_mkAuxName___closed__1;
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
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
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
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_22 = l_Lean_Meta_mkAuxName___closed__1;
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
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
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
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_22 = l_Lean_Meta_mkAuxName___closed__1;
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
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
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
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_22 = l_Lean_Meta_mkAuxName___closed__1;
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
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
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
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_22 = l_Lean_Meta_mkAuxName___closed__1;
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
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
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
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_22 = l_Lean_Meta_mkAuxName___closed__1;
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
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
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
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_22 = l_Lean_Meta_mkAuxName___closed__1;
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
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
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
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_22 = l_Lean_Meta_mkAuxName___closed__1;
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
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
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
x_26 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
x_28 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_22 = l_Lean_Meta_mkAuxName___closed__1;
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
x_25 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
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
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_7 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__6;
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__8;
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
x_1 = lean_mk_string("don't know how to generate parenthesizer for non-parser combinator '");
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
lean_object* x_1; 
x_1 = lean_mk_string("don't know how to generate parenthesizer for non-definition '");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__2___boxed), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__5___boxed), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__8___boxed), 6, 2);
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
x_2 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__11___boxed), 6, 2);
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
x_2 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__14___boxed), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__16), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__18___boxed), 6, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__21___boxed), 6, 2);
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
x_2 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__24___boxed), 6, 2);
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
x_2 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__27___boxed), 6, 2);
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
x_2 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__30___boxed), 6, 2);
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
x_2 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
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
x_29 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_28, x_27, x_19);
lean_dec(x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_41 = l_Lean_Expr_isConstOf(x_38, x_40);
lean_dec(x_38);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_19);
lean_inc(x_2);
lean_inc(x_5);
x_42 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_51 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_box(0);
x_53 = l_Lean_Meta_throwOther___rarg(x_51, x_52, x_2, x_44);
lean_dec(x_2);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_5);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_dec(x_42);
x_55 = lean_ctor_get(x_43, 0);
lean_inc(x_55);
lean_dec(x_43);
x_1 = x_55;
x_3 = x_54;
goto _start;
}
}
else
{
uint8_t x_57; 
lean_dec(x_5);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_42);
if (x_57 == 0)
{
return x_42;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_42, 0);
x_59 = lean_ctor_get(x_42, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_42);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; 
x_61 = l_Lean_ConstantInfo_value_x3f(x_33);
lean_dec(x_33);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_19);
x_62 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_63 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__9;
x_66 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_68 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_box(0);
x_70 = l_Lean_Meta_throwOther___rarg(x_68, x_69, x_2, x_39);
lean_dec(x_2);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_5);
x_71 = lean_ctor_get(x_61, 0);
lean_inc(x_71);
lean_dec(x_61);
x_72 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_71);
lean_inc(x_2);
x_73 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_72, x_2, x_39);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_115; lean_object* x_116; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_115 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__10;
lean_inc(x_2);
x_116 = l_Lean_Meta_forallTelescope___rarg(x_35, x_115, x_2, x_75);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_31);
x_119 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_119, 0, x_31);
lean_ctor_set(x_119, 1, x_29);
lean_ctor_set(x_119, 2, x_117);
x_120 = lean_box(0);
x_121 = 0;
x_122 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_74);
lean_ctor_set(x_122, 2, x_120);
lean_ctor_set_uint8(x_122, sizeof(void*)*3, x_121);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_ctor_get(x_118, 0);
lean_inc(x_124);
x_125 = l_Lean_Options_empty;
x_126 = l_Lean_Environment_addAndCompile(x_124, x_125, x_123);
lean_dec(x_123);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_19);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec(x_126);
x_128 = l_Lean_KernelException_toMessageData(x_127, x_125);
x_129 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_128);
x_130 = l_Lean_Format_pretty(x_129, x_125);
x_131 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_133 = lean_box(0);
x_134 = l_Lean_Meta_throwOther___rarg(x_132, x_133, x_2, x_118);
lean_dec(x_2);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
return x_134;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_134);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
else
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_126, 0);
lean_inc(x_139);
lean_dec(x_126);
x_76 = x_139;
x_77 = x_118;
goto block_114;
}
}
else
{
uint8_t x_140; 
lean_dec(x_74);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_2);
x_140 = !lean_is_exclusive(x_116);
if (x_140 == 0)
{
return x_116;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_116, 0);
x_142 = lean_ctor_get(x_116, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_116);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
block_114:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_78 = lean_mk_syntax_ident(x_19);
x_79 = l_Lean_mkOptionalNode___closed__2;
x_80 = lean_array_push(x_79, x_78);
x_81 = l_Lean_nullKind;
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
x_84 = 1;
x_85 = lean_box(0);
lean_inc(x_31);
x_86 = lean_add_attribute(x_76, x_31, x_83, x_82, x_84, x_85);
x_87 = lean_box(0);
x_88 = l_Lean_mkConst(x_31, x_87);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_86, 0);
lean_inc(x_101);
lean_dec(x_86);
x_102 = l_Lean_Meta_setEnv(x_101, x_2, x_77);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_89 = x_103;
goto block_100;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_dec(x_88);
lean_dec(x_26);
x_104 = lean_ctor_get(x_86, 0);
lean_inc(x_104);
lean_dec(x_86);
x_105 = lean_io_error_to_string(x_104);
x_106 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_box(0);
x_109 = l_Lean_Meta_throwOther___rarg(x_107, x_108, x_2, x_77);
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
return x_109;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_109);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
block_100:
{
lean_object* x_90; 
lean_inc(x_2);
lean_inc(x_88);
x_90 = l_Lean_Meta_inferType(x_88, x_2, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_mkAppStx___closed__2;
x_94 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__1___boxed), 8, 4);
lean_closure_set(x_94, 0, x_36);
lean_closure_set(x_94, 1, x_93);
lean_closure_set(x_94, 2, x_26);
lean_closure_set(x_94, 3, x_88);
x_95 = l_Lean_Meta_forallTelescope___rarg(x_91, x_94, x_2, x_92);
return x_95;
}
else
{
uint8_t x_96; 
lean_dec(x_88);
lean_dec(x_26);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_90);
if (x_96 == 0)
{
return x_90;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_90, 0);
x_98 = lean_ctor_get(x_90, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_90);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_73);
if (x_144 == 0)
{
return x_73;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_73, 0);
x_146 = lean_ctor_get(x_73, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_73);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_2);
x_148 = !lean_is_exclusive(x_37);
if (x_148 == 0)
{
return x_37;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_37, 0);
x_150 = lean_ctor_get(x_37, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_37);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_2);
x_152 = !lean_is_exclusive(x_32);
if (x_152 == 0)
{
return x_32;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_32, 0);
x_154 = lean_ctor_get(x_32, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_32);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_19);
lean_dec(x_5);
x_156 = lean_ctor_get(x_29, 0);
lean_inc(x_156);
lean_dec(x_29);
x_157 = lean_box(0);
x_158 = l_Lean_mkConst(x_156, x_157);
lean_inc(x_2);
lean_inc(x_158);
x_159 = l_Lean_Meta_inferType(x_158, x_2, x_6);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__3___boxed), 6, 2);
lean_closure_set(x_162, 0, x_26);
lean_closure_set(x_162, 1, x_158);
x_163 = l_Lean_Meta_forallTelescope___rarg(x_160, x_162, x_2, x_161);
return x_163;
}
else
{
uint8_t x_164; 
lean_dec(x_158);
lean_dec(x_26);
lean_dec(x_2);
x_164 = !lean_is_exclusive(x_159);
if (x_164 == 0)
{
return x_159;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_159, 0);
x_166 = lean_ctor_get(x_159, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_159);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
else
{
lean_object* x_168; 
lean_dec(x_7);
x_168 = lean_box(0);
x_8 = x_168;
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
x_14 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
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
uint8_t x_169; 
lean_dec(x_2);
x_169 = !lean_is_exclusive(x_4);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_4, 0);
lean_dec(x_170);
return x_4;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_4, 1);
lean_inc(x_171);
lean_dec(x_4);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_5);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
case 2:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_4, 1);
lean_inc(x_173);
lean_dec(x_4);
x_174 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_174) == 4)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_186 = lean_ctor_get(x_174, 0);
lean_inc(x_186);
lean_dec(x_174);
x_187 = lean_unsigned_to_nat(0u);
x_188 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_187);
x_189 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_188);
x_190 = lean_mk_array(x_188, x_189);
x_191 = lean_unsigned_to_nat(1u);
x_192 = lean_nat_sub(x_188, x_191);
lean_dec(x_188);
lean_inc(x_5);
x_193 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_190, x_192);
x_194 = lean_ctor_get(x_173, 0);
lean_inc(x_194);
x_195 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_196 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_195, x_194, x_186);
lean_dec(x_194);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_198 = l_Lean_Name_append___main(x_186, x_197);
lean_inc(x_186);
x_199 = l_Lean_Meta_getConstInfo(x_186, x_2, x_173);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = l_Lean_ConstantInfo_type(x_200);
x_203 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_202);
x_204 = l_Lean_Meta_forallTelescope___rarg(x_202, x_203, x_2, x_201);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_208 = l_Lean_Expr_isConstOf(x_205, x_207);
lean_dec(x_205);
if (x_208 == 0)
{
lean_object* x_209; 
lean_dec(x_202);
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_193);
lean_dec(x_186);
lean_inc(x_2);
lean_inc(x_5);
x_209 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_206);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_213 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_214, 0, x_213);
x_215 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_216 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_214);
x_217 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_218 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
x_219 = lean_box(0);
x_220 = l_Lean_Meta_throwOther___rarg(x_218, x_219, x_2, x_211);
lean_dec(x_2);
return x_220;
}
else
{
lean_object* x_221; lean_object* x_222; 
lean_dec(x_5);
x_221 = lean_ctor_get(x_209, 1);
lean_inc(x_221);
lean_dec(x_209);
x_222 = lean_ctor_get(x_210, 0);
lean_inc(x_222);
lean_dec(x_210);
x_1 = x_222;
x_3 = x_221;
goto _start;
}
}
else
{
uint8_t x_224; 
lean_dec(x_5);
lean_dec(x_2);
x_224 = !lean_is_exclusive(x_209);
if (x_224 == 0)
{
return x_209;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_209, 0);
x_226 = lean_ctor_get(x_209, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_209);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
lean_object* x_228; 
x_228 = l_Lean_ConstantInfo_value_x3f(x_200);
lean_dec(x_200);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_202);
lean_dec(x_198);
lean_dec(x_193);
lean_dec(x_186);
x_229 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_230 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_230, 0, x_229);
x_231 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_231, 0, x_230);
x_232 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__9;
x_233 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
x_234 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_235 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_box(0);
x_237 = l_Lean_Meta_throwOther___rarg(x_235, x_236, x_2, x_206);
lean_dec(x_2);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_5);
x_238 = lean_ctor_get(x_228, 0);
lean_inc(x_238);
lean_dec(x_228);
x_239 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_238);
lean_inc(x_2);
x_240 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_239, x_2, x_206);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_282; lean_object* x_283; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_282 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__11;
lean_inc(x_2);
x_283 = l_Lean_Meta_forallTelescope___rarg(x_202, x_282, x_2, x_242);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
lean_inc(x_198);
x_286 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_286, 0, x_198);
lean_ctor_set(x_286, 1, x_196);
lean_ctor_set(x_286, 2, x_284);
x_287 = lean_box(0);
x_288 = 0;
x_289 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_241);
lean_ctor_set(x_289, 2, x_287);
lean_ctor_set_uint8(x_289, sizeof(void*)*3, x_288);
x_290 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_290, 0, x_289);
x_291 = lean_ctor_get(x_285, 0);
lean_inc(x_291);
x_292 = l_Lean_Options_empty;
x_293 = l_Lean_Environment_addAndCompile(x_291, x_292, x_290);
lean_dec(x_290);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; 
lean_dec(x_198);
lean_dec(x_193);
lean_dec(x_186);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
lean_dec(x_293);
x_295 = l_Lean_KernelException_toMessageData(x_294, x_292);
x_296 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_295);
x_297 = l_Lean_Format_pretty(x_296, x_292);
x_298 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_298, 0, x_297);
x_299 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_299, 0, x_298);
x_300 = lean_box(0);
x_301 = l_Lean_Meta_throwOther___rarg(x_299, x_300, x_2, x_285);
lean_dec(x_2);
x_302 = !lean_is_exclusive(x_301);
if (x_302 == 0)
{
return x_301;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_301, 0);
x_304 = lean_ctor_get(x_301, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_301);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
else
{
lean_object* x_306; 
x_306 = lean_ctor_get(x_293, 0);
lean_inc(x_306);
lean_dec(x_293);
x_243 = x_306;
x_244 = x_285;
goto block_281;
}
}
else
{
uint8_t x_307; 
lean_dec(x_241);
lean_dec(x_198);
lean_dec(x_193);
lean_dec(x_186);
lean_dec(x_2);
x_307 = !lean_is_exclusive(x_283);
if (x_307 == 0)
{
return x_283;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_283, 0);
x_309 = lean_ctor_get(x_283, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_283);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
block_281:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_245 = lean_mk_syntax_ident(x_186);
x_246 = l_Lean_mkOptionalNode___closed__2;
x_247 = lean_array_push(x_246, x_245);
x_248 = l_Lean_nullKind;
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
x_250 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
x_251 = 1;
x_252 = lean_box(0);
lean_inc(x_198);
x_253 = lean_add_attribute(x_243, x_198, x_250, x_249, x_251, x_252);
x_254 = lean_box(0);
x_255 = l_Lean_mkConst(x_198, x_254);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_253, 0);
lean_inc(x_268);
lean_dec(x_253);
x_269 = l_Lean_Meta_setEnv(x_268, x_2, x_244);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec(x_269);
x_256 = x_270;
goto block_267;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
lean_dec(x_255);
lean_dec(x_193);
x_271 = lean_ctor_get(x_253, 0);
lean_inc(x_271);
lean_dec(x_253);
x_272 = lean_io_error_to_string(x_271);
x_273 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_273, 0, x_272);
x_274 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_274, 0, x_273);
x_275 = lean_box(0);
x_276 = l_Lean_Meta_throwOther___rarg(x_274, x_275, x_2, x_244);
lean_dec(x_2);
x_277 = !lean_is_exclusive(x_276);
if (x_277 == 0)
{
return x_276;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_276, 0);
x_279 = lean_ctor_get(x_276, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_276);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
return x_280;
}
}
block_267:
{
lean_object* x_257; 
lean_inc(x_2);
lean_inc(x_255);
x_257 = l_Lean_Meta_inferType(x_255, x_2, x_256);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = l_Lean_mkAppStx___closed__2;
x_261 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__4___boxed), 8, 4);
lean_closure_set(x_261, 0, x_203);
lean_closure_set(x_261, 1, x_260);
lean_closure_set(x_261, 2, x_193);
lean_closure_set(x_261, 3, x_255);
x_262 = l_Lean_Meta_forallTelescope___rarg(x_258, x_261, x_2, x_259);
return x_262;
}
else
{
uint8_t x_263; 
lean_dec(x_255);
lean_dec(x_193);
lean_dec(x_2);
x_263 = !lean_is_exclusive(x_257);
if (x_263 == 0)
{
return x_257;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_257, 0);
x_265 = lean_ctor_get(x_257, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_257);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
}
}
else
{
uint8_t x_311; 
lean_dec(x_202);
lean_dec(x_198);
lean_dec(x_193);
lean_dec(x_186);
lean_dec(x_2);
x_311 = !lean_is_exclusive(x_240);
if (x_311 == 0)
{
return x_240;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_240, 0);
x_313 = lean_ctor_get(x_240, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_240);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
}
}
}
}
else
{
uint8_t x_315; 
lean_dec(x_202);
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_193);
lean_dec(x_186);
lean_dec(x_5);
lean_dec(x_2);
x_315 = !lean_is_exclusive(x_204);
if (x_315 == 0)
{
return x_204;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_204, 0);
x_317 = lean_ctor_get(x_204, 1);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_204);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
return x_318;
}
}
}
else
{
uint8_t x_319; 
lean_dec(x_198);
lean_dec(x_193);
lean_dec(x_186);
lean_dec(x_5);
lean_dec(x_2);
x_319 = !lean_is_exclusive(x_199);
if (x_319 == 0)
{
return x_199;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_199, 0);
x_321 = lean_ctor_get(x_199, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_199);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_186);
lean_dec(x_5);
x_323 = lean_ctor_get(x_196, 0);
lean_inc(x_323);
lean_dec(x_196);
x_324 = lean_box(0);
x_325 = l_Lean_mkConst(x_323, x_324);
lean_inc(x_2);
lean_inc(x_325);
x_326 = l_Lean_Meta_inferType(x_325, x_2, x_173);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
lean_dec(x_326);
x_329 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__6___boxed), 6, 2);
lean_closure_set(x_329, 0, x_193);
lean_closure_set(x_329, 1, x_325);
x_330 = l_Lean_Meta_forallTelescope___rarg(x_327, x_329, x_2, x_328);
return x_330;
}
else
{
uint8_t x_331; 
lean_dec(x_325);
lean_dec(x_193);
lean_dec(x_2);
x_331 = !lean_is_exclusive(x_326);
if (x_331 == 0)
{
return x_326;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_326, 0);
x_333 = lean_ctor_get(x_326, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_326);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
return x_334;
}
}
}
}
else
{
lean_object* x_335; 
lean_dec(x_174);
x_335 = lean_box(0);
x_175 = x_335;
goto block_185;
}
block_185:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_175);
x_176 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_177 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_177, 0, x_176);
x_178 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_180 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
x_181 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_182 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_box(0);
x_184 = l_Lean_Meta_throwOther___rarg(x_182, x_183, x_2, x_173);
lean_dec(x_2);
return x_184;
}
}
case 3:
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_4, 1);
lean_inc(x_336);
lean_dec(x_4);
x_337 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_337) == 4)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_349 = lean_ctor_get(x_337, 0);
lean_inc(x_349);
lean_dec(x_337);
x_350 = lean_unsigned_to_nat(0u);
x_351 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_350);
x_352 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_351);
x_353 = lean_mk_array(x_351, x_352);
x_354 = lean_unsigned_to_nat(1u);
x_355 = lean_nat_sub(x_351, x_354);
lean_dec(x_351);
lean_inc(x_5);
x_356 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_353, x_355);
x_357 = lean_ctor_get(x_336, 0);
lean_inc(x_357);
x_358 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_359 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_358, x_357, x_349);
lean_dec(x_357);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_361 = l_Lean_Name_append___main(x_349, x_360);
lean_inc(x_349);
x_362 = l_Lean_Meta_getConstInfo(x_349, x_2, x_336);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
lean_dec(x_362);
x_365 = l_Lean_ConstantInfo_type(x_363);
x_366 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_365);
x_367 = l_Lean_Meta_forallTelescope___rarg(x_365, x_366, x_2, x_364);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec(x_367);
x_370 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_371 = l_Lean_Expr_isConstOf(x_368, x_370);
lean_dec(x_368);
if (x_371 == 0)
{
lean_object* x_372; 
lean_dec(x_365);
lean_dec(x_363);
lean_dec(x_361);
lean_dec(x_356);
lean_dec(x_349);
lean_inc(x_2);
lean_inc(x_5);
x_372 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_369);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_374 = lean_ctor_get(x_372, 1);
lean_inc(x_374);
lean_dec(x_372);
x_375 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_376 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_376, 0, x_375);
x_377 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_377, 0, x_376);
x_378 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_379 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_377);
x_380 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_381 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
x_382 = lean_box(0);
x_383 = l_Lean_Meta_throwOther___rarg(x_381, x_382, x_2, x_374);
lean_dec(x_2);
return x_383;
}
else
{
lean_object* x_384; lean_object* x_385; 
lean_dec(x_5);
x_384 = lean_ctor_get(x_372, 1);
lean_inc(x_384);
lean_dec(x_372);
x_385 = lean_ctor_get(x_373, 0);
lean_inc(x_385);
lean_dec(x_373);
x_1 = x_385;
x_3 = x_384;
goto _start;
}
}
else
{
uint8_t x_387; 
lean_dec(x_5);
lean_dec(x_2);
x_387 = !lean_is_exclusive(x_372);
if (x_387 == 0)
{
return x_372;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_388 = lean_ctor_get(x_372, 0);
x_389 = lean_ctor_get(x_372, 1);
lean_inc(x_389);
lean_inc(x_388);
lean_dec(x_372);
x_390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_390, 0, x_388);
lean_ctor_set(x_390, 1, x_389);
return x_390;
}
}
}
else
{
lean_object* x_391; 
x_391 = l_Lean_ConstantInfo_value_x3f(x_363);
lean_dec(x_363);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_365);
lean_dec(x_361);
lean_dec(x_356);
lean_dec(x_349);
x_392 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_393 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_393, 0, x_392);
x_394 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_394, 0, x_393);
x_395 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__9;
x_396 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_394);
x_397 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_398 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_397);
x_399 = lean_box(0);
x_400 = l_Lean_Meta_throwOther___rarg(x_398, x_399, x_2, x_369);
lean_dec(x_2);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_5);
x_401 = lean_ctor_get(x_391, 0);
lean_inc(x_401);
lean_dec(x_391);
x_402 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_401);
lean_inc(x_2);
x_403 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_402, x_2, x_369);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_445; lean_object* x_446; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
x_445 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__12;
lean_inc(x_2);
x_446 = l_Lean_Meta_forallTelescope___rarg(x_365, x_445, x_2, x_405);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_446, 1);
lean_inc(x_448);
lean_dec(x_446);
lean_inc(x_361);
x_449 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_449, 0, x_361);
lean_ctor_set(x_449, 1, x_359);
lean_ctor_set(x_449, 2, x_447);
x_450 = lean_box(0);
x_451 = 0;
x_452 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_452, 0, x_449);
lean_ctor_set(x_452, 1, x_404);
lean_ctor_set(x_452, 2, x_450);
lean_ctor_set_uint8(x_452, sizeof(void*)*3, x_451);
x_453 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_453, 0, x_452);
x_454 = lean_ctor_get(x_448, 0);
lean_inc(x_454);
x_455 = l_Lean_Options_empty;
x_456 = l_Lean_Environment_addAndCompile(x_454, x_455, x_453);
lean_dec(x_453);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; 
lean_dec(x_361);
lean_dec(x_356);
lean_dec(x_349);
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
lean_dec(x_456);
x_458 = l_Lean_KernelException_toMessageData(x_457, x_455);
x_459 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_458);
x_460 = l_Lean_Format_pretty(x_459, x_455);
x_461 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_461, 0, x_460);
x_462 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_462, 0, x_461);
x_463 = lean_box(0);
x_464 = l_Lean_Meta_throwOther___rarg(x_462, x_463, x_2, x_448);
lean_dec(x_2);
x_465 = !lean_is_exclusive(x_464);
if (x_465 == 0)
{
return x_464;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_466 = lean_ctor_get(x_464, 0);
x_467 = lean_ctor_get(x_464, 1);
lean_inc(x_467);
lean_inc(x_466);
lean_dec(x_464);
x_468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_468, 0, x_466);
lean_ctor_set(x_468, 1, x_467);
return x_468;
}
}
else
{
lean_object* x_469; 
x_469 = lean_ctor_get(x_456, 0);
lean_inc(x_469);
lean_dec(x_456);
x_406 = x_469;
x_407 = x_448;
goto block_444;
}
}
else
{
uint8_t x_470; 
lean_dec(x_404);
lean_dec(x_361);
lean_dec(x_356);
lean_dec(x_349);
lean_dec(x_2);
x_470 = !lean_is_exclusive(x_446);
if (x_470 == 0)
{
return x_446;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = lean_ctor_get(x_446, 0);
x_472 = lean_ctor_get(x_446, 1);
lean_inc(x_472);
lean_inc(x_471);
lean_dec(x_446);
x_473 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_473, 0, x_471);
lean_ctor_set(x_473, 1, x_472);
return x_473;
}
}
block_444:
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_408 = lean_mk_syntax_ident(x_349);
x_409 = l_Lean_mkOptionalNode___closed__2;
x_410 = lean_array_push(x_409, x_408);
x_411 = l_Lean_nullKind;
x_412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_410);
x_413 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
x_414 = 1;
x_415 = lean_box(0);
lean_inc(x_361);
x_416 = lean_add_attribute(x_406, x_361, x_413, x_412, x_414, x_415);
x_417 = lean_box(0);
x_418 = l_Lean_mkConst(x_361, x_417);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_416, 0);
lean_inc(x_431);
lean_dec(x_416);
x_432 = l_Lean_Meta_setEnv(x_431, x_2, x_407);
x_433 = lean_ctor_get(x_432, 1);
lean_inc(x_433);
lean_dec(x_432);
x_419 = x_433;
goto block_430;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; 
lean_dec(x_418);
lean_dec(x_356);
x_434 = lean_ctor_get(x_416, 0);
lean_inc(x_434);
lean_dec(x_416);
x_435 = lean_io_error_to_string(x_434);
x_436 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_436, 0, x_435);
x_437 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_437, 0, x_436);
x_438 = lean_box(0);
x_439 = l_Lean_Meta_throwOther___rarg(x_437, x_438, x_2, x_407);
lean_dec(x_2);
x_440 = !lean_is_exclusive(x_439);
if (x_440 == 0)
{
return x_439;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_439, 0);
x_442 = lean_ctor_get(x_439, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_439);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
return x_443;
}
}
block_430:
{
lean_object* x_420; 
lean_inc(x_2);
lean_inc(x_418);
x_420 = l_Lean_Meta_inferType(x_418, x_2, x_419);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = l_Lean_mkAppStx___closed__2;
x_424 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__7___boxed), 8, 4);
lean_closure_set(x_424, 0, x_366);
lean_closure_set(x_424, 1, x_423);
lean_closure_set(x_424, 2, x_356);
lean_closure_set(x_424, 3, x_418);
x_425 = l_Lean_Meta_forallTelescope___rarg(x_421, x_424, x_2, x_422);
return x_425;
}
else
{
uint8_t x_426; 
lean_dec(x_418);
lean_dec(x_356);
lean_dec(x_2);
x_426 = !lean_is_exclusive(x_420);
if (x_426 == 0)
{
return x_420;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_420, 0);
x_428 = lean_ctor_get(x_420, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_420);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
}
}
}
else
{
uint8_t x_474; 
lean_dec(x_365);
lean_dec(x_361);
lean_dec(x_356);
lean_dec(x_349);
lean_dec(x_2);
x_474 = !lean_is_exclusive(x_403);
if (x_474 == 0)
{
return x_403;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = lean_ctor_get(x_403, 0);
x_476 = lean_ctor_get(x_403, 1);
lean_inc(x_476);
lean_inc(x_475);
lean_dec(x_403);
x_477 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_477, 0, x_475);
lean_ctor_set(x_477, 1, x_476);
return x_477;
}
}
}
}
}
else
{
uint8_t x_478; 
lean_dec(x_365);
lean_dec(x_363);
lean_dec(x_361);
lean_dec(x_356);
lean_dec(x_349);
lean_dec(x_5);
lean_dec(x_2);
x_478 = !lean_is_exclusive(x_367);
if (x_478 == 0)
{
return x_367;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_479 = lean_ctor_get(x_367, 0);
x_480 = lean_ctor_get(x_367, 1);
lean_inc(x_480);
lean_inc(x_479);
lean_dec(x_367);
x_481 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_481, 0, x_479);
lean_ctor_set(x_481, 1, x_480);
return x_481;
}
}
}
else
{
uint8_t x_482; 
lean_dec(x_361);
lean_dec(x_356);
lean_dec(x_349);
lean_dec(x_5);
lean_dec(x_2);
x_482 = !lean_is_exclusive(x_362);
if (x_482 == 0)
{
return x_362;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_483 = lean_ctor_get(x_362, 0);
x_484 = lean_ctor_get(x_362, 1);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_362);
x_485 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set(x_485, 1, x_484);
return x_485;
}
}
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
lean_dec(x_349);
lean_dec(x_5);
x_486 = lean_ctor_get(x_359, 0);
lean_inc(x_486);
lean_dec(x_359);
x_487 = lean_box(0);
x_488 = l_Lean_mkConst(x_486, x_487);
lean_inc(x_2);
lean_inc(x_488);
x_489 = l_Lean_Meta_inferType(x_488, x_2, x_336);
if (lean_obj_tag(x_489) == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_490 = lean_ctor_get(x_489, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_489, 1);
lean_inc(x_491);
lean_dec(x_489);
x_492 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__9___boxed), 6, 2);
lean_closure_set(x_492, 0, x_356);
lean_closure_set(x_492, 1, x_488);
x_493 = l_Lean_Meta_forallTelescope___rarg(x_490, x_492, x_2, x_491);
return x_493;
}
else
{
uint8_t x_494; 
lean_dec(x_488);
lean_dec(x_356);
lean_dec(x_2);
x_494 = !lean_is_exclusive(x_489);
if (x_494 == 0)
{
return x_489;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_495 = lean_ctor_get(x_489, 0);
x_496 = lean_ctor_get(x_489, 1);
lean_inc(x_496);
lean_inc(x_495);
lean_dec(x_489);
x_497 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_497, 0, x_495);
lean_ctor_set(x_497, 1, x_496);
return x_497;
}
}
}
}
else
{
lean_object* x_498; 
lean_dec(x_337);
x_498 = lean_box(0);
x_338 = x_498;
goto block_348;
}
block_348:
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_338);
x_339 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_340 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_340, 0, x_339);
x_341 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_341, 0, x_340);
x_342 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_343 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_341);
x_344 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_345 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
x_346 = lean_box(0);
x_347 = l_Lean_Meta_throwOther___rarg(x_345, x_346, x_2, x_336);
lean_dec(x_2);
return x_347;
}
}
case 4:
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_499 = lean_ctor_get(x_4, 1);
lean_inc(x_499);
lean_dec(x_4);
x_500 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_500) == 4)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_512 = lean_ctor_get(x_500, 0);
lean_inc(x_512);
lean_dec(x_500);
x_513 = lean_unsigned_to_nat(0u);
x_514 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_513);
x_515 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_514);
x_516 = lean_mk_array(x_514, x_515);
x_517 = lean_unsigned_to_nat(1u);
x_518 = lean_nat_sub(x_514, x_517);
lean_dec(x_514);
lean_inc(x_5);
x_519 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_516, x_518);
x_520 = lean_ctor_get(x_499, 0);
lean_inc(x_520);
x_521 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_522 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_521, x_520, x_512);
lean_dec(x_520);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_523 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_524 = l_Lean_Name_append___main(x_512, x_523);
lean_inc(x_512);
x_525 = l_Lean_Meta_getConstInfo(x_512, x_2, x_499);
if (lean_obj_tag(x_525) == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_525, 1);
lean_inc(x_527);
lean_dec(x_525);
x_528 = l_Lean_ConstantInfo_type(x_526);
x_529 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_528);
x_530 = l_Lean_Meta_forallTelescope___rarg(x_528, x_529, x_2, x_527);
if (lean_obj_tag(x_530) == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; uint8_t x_534; 
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_530, 1);
lean_inc(x_532);
lean_dec(x_530);
x_533 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_534 = l_Lean_Expr_isConstOf(x_531, x_533);
lean_dec(x_531);
if (x_534 == 0)
{
lean_object* x_535; 
lean_dec(x_528);
lean_dec(x_526);
lean_dec(x_524);
lean_dec(x_519);
lean_dec(x_512);
lean_inc(x_2);
lean_inc(x_5);
x_535 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_532);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; 
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_537 = lean_ctor_get(x_535, 1);
lean_inc(x_537);
lean_dec(x_535);
x_538 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_539 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_539, 0, x_538);
x_540 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_540, 0, x_539);
x_541 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_542 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_542, 0, x_541);
lean_ctor_set(x_542, 1, x_540);
x_543 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_544 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_543);
x_545 = lean_box(0);
x_546 = l_Lean_Meta_throwOther___rarg(x_544, x_545, x_2, x_537);
lean_dec(x_2);
return x_546;
}
else
{
lean_object* x_547; lean_object* x_548; 
lean_dec(x_5);
x_547 = lean_ctor_get(x_535, 1);
lean_inc(x_547);
lean_dec(x_535);
x_548 = lean_ctor_get(x_536, 0);
lean_inc(x_548);
lean_dec(x_536);
x_1 = x_548;
x_3 = x_547;
goto _start;
}
}
else
{
uint8_t x_550; 
lean_dec(x_5);
lean_dec(x_2);
x_550 = !lean_is_exclusive(x_535);
if (x_550 == 0)
{
return x_535;
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_551 = lean_ctor_get(x_535, 0);
x_552 = lean_ctor_get(x_535, 1);
lean_inc(x_552);
lean_inc(x_551);
lean_dec(x_535);
x_553 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_553, 0, x_551);
lean_ctor_set(x_553, 1, x_552);
return x_553;
}
}
}
else
{
lean_object* x_554; 
x_554 = l_Lean_ConstantInfo_value_x3f(x_526);
lean_dec(x_526);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_528);
lean_dec(x_524);
lean_dec(x_519);
lean_dec(x_512);
x_555 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_556 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_556, 0, x_555);
x_557 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_557, 0, x_556);
x_558 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__9;
x_559 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_559, 0, x_558);
lean_ctor_set(x_559, 1, x_557);
x_560 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_561 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_561, 0, x_559);
lean_ctor_set(x_561, 1, x_560);
x_562 = lean_box(0);
x_563 = l_Lean_Meta_throwOther___rarg(x_561, x_562, x_2, x_532);
lean_dec(x_2);
return x_563;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
lean_dec(x_5);
x_564 = lean_ctor_get(x_554, 0);
lean_inc(x_564);
lean_dec(x_554);
x_565 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_564);
lean_inc(x_2);
x_566 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_565, x_2, x_532);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_608; lean_object* x_609; 
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_566, 1);
lean_inc(x_568);
lean_dec(x_566);
x_608 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__13;
lean_inc(x_2);
x_609 = l_Lean_Meta_forallTelescope___rarg(x_528, x_608, x_2, x_568);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; uint8_t x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
lean_dec(x_609);
lean_inc(x_524);
x_612 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_612, 0, x_524);
lean_ctor_set(x_612, 1, x_522);
lean_ctor_set(x_612, 2, x_610);
x_613 = lean_box(0);
x_614 = 0;
x_615 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_615, 0, x_612);
lean_ctor_set(x_615, 1, x_567);
lean_ctor_set(x_615, 2, x_613);
lean_ctor_set_uint8(x_615, sizeof(void*)*3, x_614);
x_616 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_616, 0, x_615);
x_617 = lean_ctor_get(x_611, 0);
lean_inc(x_617);
x_618 = l_Lean_Options_empty;
x_619 = l_Lean_Environment_addAndCompile(x_617, x_618, x_616);
lean_dec(x_616);
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; uint8_t x_628; 
lean_dec(x_524);
lean_dec(x_519);
lean_dec(x_512);
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
lean_dec(x_619);
x_621 = l_Lean_KernelException_toMessageData(x_620, x_618);
x_622 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_621);
x_623 = l_Lean_Format_pretty(x_622, x_618);
x_624 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_624, 0, x_623);
x_625 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_625, 0, x_624);
x_626 = lean_box(0);
x_627 = l_Lean_Meta_throwOther___rarg(x_625, x_626, x_2, x_611);
lean_dec(x_2);
x_628 = !lean_is_exclusive(x_627);
if (x_628 == 0)
{
return x_627;
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_629 = lean_ctor_get(x_627, 0);
x_630 = lean_ctor_get(x_627, 1);
lean_inc(x_630);
lean_inc(x_629);
lean_dec(x_627);
x_631 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_631, 0, x_629);
lean_ctor_set(x_631, 1, x_630);
return x_631;
}
}
else
{
lean_object* x_632; 
x_632 = lean_ctor_get(x_619, 0);
lean_inc(x_632);
lean_dec(x_619);
x_569 = x_632;
x_570 = x_611;
goto block_607;
}
}
else
{
uint8_t x_633; 
lean_dec(x_567);
lean_dec(x_524);
lean_dec(x_519);
lean_dec(x_512);
lean_dec(x_2);
x_633 = !lean_is_exclusive(x_609);
if (x_633 == 0)
{
return x_609;
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_634 = lean_ctor_get(x_609, 0);
x_635 = lean_ctor_get(x_609, 1);
lean_inc(x_635);
lean_inc(x_634);
lean_dec(x_609);
x_636 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_636, 0, x_634);
lean_ctor_set(x_636, 1, x_635);
return x_636;
}
}
block_607:
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; uint8_t x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_571 = lean_mk_syntax_ident(x_512);
x_572 = l_Lean_mkOptionalNode___closed__2;
x_573 = lean_array_push(x_572, x_571);
x_574 = l_Lean_nullKind;
x_575 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_575, 0, x_574);
lean_ctor_set(x_575, 1, x_573);
x_576 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
x_577 = 1;
x_578 = lean_box(0);
lean_inc(x_524);
x_579 = lean_add_attribute(x_569, x_524, x_576, x_575, x_577, x_578);
x_580 = lean_box(0);
x_581 = l_Lean_mkConst(x_524, x_580);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_594 = lean_ctor_get(x_579, 0);
lean_inc(x_594);
lean_dec(x_579);
x_595 = l_Lean_Meta_setEnv(x_594, x_2, x_570);
x_596 = lean_ctor_get(x_595, 1);
lean_inc(x_596);
lean_dec(x_595);
x_582 = x_596;
goto block_593;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; uint8_t x_603; 
lean_dec(x_581);
lean_dec(x_519);
x_597 = lean_ctor_get(x_579, 0);
lean_inc(x_597);
lean_dec(x_579);
x_598 = lean_io_error_to_string(x_597);
x_599 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_599, 0, x_598);
x_600 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_600, 0, x_599);
x_601 = lean_box(0);
x_602 = l_Lean_Meta_throwOther___rarg(x_600, x_601, x_2, x_570);
lean_dec(x_2);
x_603 = !lean_is_exclusive(x_602);
if (x_603 == 0)
{
return x_602;
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_604 = lean_ctor_get(x_602, 0);
x_605 = lean_ctor_get(x_602, 1);
lean_inc(x_605);
lean_inc(x_604);
lean_dec(x_602);
x_606 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_606, 0, x_604);
lean_ctor_set(x_606, 1, x_605);
return x_606;
}
}
block_593:
{
lean_object* x_583; 
lean_inc(x_2);
lean_inc(x_581);
x_583 = l_Lean_Meta_inferType(x_581, x_2, x_582);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_583, 1);
lean_inc(x_585);
lean_dec(x_583);
x_586 = l_Lean_mkAppStx___closed__2;
x_587 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__10___boxed), 8, 4);
lean_closure_set(x_587, 0, x_529);
lean_closure_set(x_587, 1, x_586);
lean_closure_set(x_587, 2, x_519);
lean_closure_set(x_587, 3, x_581);
x_588 = l_Lean_Meta_forallTelescope___rarg(x_584, x_587, x_2, x_585);
return x_588;
}
else
{
uint8_t x_589; 
lean_dec(x_581);
lean_dec(x_519);
lean_dec(x_2);
x_589 = !lean_is_exclusive(x_583);
if (x_589 == 0)
{
return x_583;
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_590 = lean_ctor_get(x_583, 0);
x_591 = lean_ctor_get(x_583, 1);
lean_inc(x_591);
lean_inc(x_590);
lean_dec(x_583);
x_592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_591);
return x_592;
}
}
}
}
}
else
{
uint8_t x_637; 
lean_dec(x_528);
lean_dec(x_524);
lean_dec(x_519);
lean_dec(x_512);
lean_dec(x_2);
x_637 = !lean_is_exclusive(x_566);
if (x_637 == 0)
{
return x_566;
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_638 = lean_ctor_get(x_566, 0);
x_639 = lean_ctor_get(x_566, 1);
lean_inc(x_639);
lean_inc(x_638);
lean_dec(x_566);
x_640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_640, 0, x_638);
lean_ctor_set(x_640, 1, x_639);
return x_640;
}
}
}
}
}
else
{
uint8_t x_641; 
lean_dec(x_528);
lean_dec(x_526);
lean_dec(x_524);
lean_dec(x_519);
lean_dec(x_512);
lean_dec(x_5);
lean_dec(x_2);
x_641 = !lean_is_exclusive(x_530);
if (x_641 == 0)
{
return x_530;
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_642 = lean_ctor_get(x_530, 0);
x_643 = lean_ctor_get(x_530, 1);
lean_inc(x_643);
lean_inc(x_642);
lean_dec(x_530);
x_644 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_644, 0, x_642);
lean_ctor_set(x_644, 1, x_643);
return x_644;
}
}
}
else
{
uint8_t x_645; 
lean_dec(x_524);
lean_dec(x_519);
lean_dec(x_512);
lean_dec(x_5);
lean_dec(x_2);
x_645 = !lean_is_exclusive(x_525);
if (x_645 == 0)
{
return x_525;
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_646 = lean_ctor_get(x_525, 0);
x_647 = lean_ctor_get(x_525, 1);
lean_inc(x_647);
lean_inc(x_646);
lean_dec(x_525);
x_648 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_648, 0, x_646);
lean_ctor_set(x_648, 1, x_647);
return x_648;
}
}
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
lean_dec(x_512);
lean_dec(x_5);
x_649 = lean_ctor_get(x_522, 0);
lean_inc(x_649);
lean_dec(x_522);
x_650 = lean_box(0);
x_651 = l_Lean_mkConst(x_649, x_650);
lean_inc(x_2);
lean_inc(x_651);
x_652 = l_Lean_Meta_inferType(x_651, x_2, x_499);
if (lean_obj_tag(x_652) == 0)
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_652, 1);
lean_inc(x_654);
lean_dec(x_652);
x_655 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__12___boxed), 6, 2);
lean_closure_set(x_655, 0, x_519);
lean_closure_set(x_655, 1, x_651);
x_656 = l_Lean_Meta_forallTelescope___rarg(x_653, x_655, x_2, x_654);
return x_656;
}
else
{
uint8_t x_657; 
lean_dec(x_651);
lean_dec(x_519);
lean_dec(x_2);
x_657 = !lean_is_exclusive(x_652);
if (x_657 == 0)
{
return x_652;
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_658 = lean_ctor_get(x_652, 0);
x_659 = lean_ctor_get(x_652, 1);
lean_inc(x_659);
lean_inc(x_658);
lean_dec(x_652);
x_660 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_660, 0, x_658);
lean_ctor_set(x_660, 1, x_659);
return x_660;
}
}
}
}
else
{
lean_object* x_661; 
lean_dec(x_500);
x_661 = lean_box(0);
x_501 = x_661;
goto block_511;
}
block_511:
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_dec(x_501);
x_502 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_503 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_503, 0, x_502);
x_504 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_504, 0, x_503);
x_505 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_506 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_504);
x_507 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_508 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_508, 0, x_506);
lean_ctor_set(x_508, 1, x_507);
x_509 = lean_box(0);
x_510 = l_Lean_Meta_throwOther___rarg(x_508, x_509, x_2, x_499);
lean_dec(x_2);
return x_510;
}
}
case 5:
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_662 = lean_ctor_get(x_4, 1);
lean_inc(x_662);
lean_dec(x_4);
x_663 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_663) == 4)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_675 = lean_ctor_get(x_663, 0);
lean_inc(x_675);
lean_dec(x_663);
x_676 = lean_unsigned_to_nat(0u);
x_677 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_676);
x_678 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_677);
x_679 = lean_mk_array(x_677, x_678);
x_680 = lean_unsigned_to_nat(1u);
x_681 = lean_nat_sub(x_677, x_680);
lean_dec(x_677);
lean_inc(x_5);
x_682 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_679, x_681);
x_683 = lean_ctor_get(x_662, 0);
lean_inc(x_683);
x_684 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_685 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_684, x_683, x_675);
lean_dec(x_683);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_686 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_687 = l_Lean_Name_append___main(x_675, x_686);
lean_inc(x_675);
x_688 = l_Lean_Meta_getConstInfo(x_675, x_2, x_662);
if (lean_obj_tag(x_688) == 0)
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_688, 1);
lean_inc(x_690);
lean_dec(x_688);
x_691 = l_Lean_ConstantInfo_type(x_689);
x_692 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_691);
x_693 = l_Lean_Meta_forallTelescope___rarg(x_691, x_692, x_2, x_690);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; uint8_t x_697; 
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_693, 1);
lean_inc(x_695);
lean_dec(x_693);
x_696 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_697 = l_Lean_Expr_isConstOf(x_694, x_696);
lean_dec(x_694);
if (x_697 == 0)
{
lean_object* x_698; 
lean_dec(x_691);
lean_dec(x_689);
lean_dec(x_687);
lean_dec(x_682);
lean_dec(x_675);
lean_inc(x_2);
lean_inc(x_5);
x_698 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_695);
if (lean_obj_tag(x_698) == 0)
{
lean_object* x_699; 
x_699 = lean_ctor_get(x_698, 0);
lean_inc(x_699);
if (lean_obj_tag(x_699) == 0)
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
x_700 = lean_ctor_get(x_698, 1);
lean_inc(x_700);
lean_dec(x_698);
x_701 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_702 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_702, 0, x_701);
x_703 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_703, 0, x_702);
x_704 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_705 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_705, 0, x_704);
lean_ctor_set(x_705, 1, x_703);
x_706 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_707 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_707, 0, x_705);
lean_ctor_set(x_707, 1, x_706);
x_708 = lean_box(0);
x_709 = l_Lean_Meta_throwOther___rarg(x_707, x_708, x_2, x_700);
lean_dec(x_2);
return x_709;
}
else
{
lean_object* x_710; lean_object* x_711; 
lean_dec(x_5);
x_710 = lean_ctor_get(x_698, 1);
lean_inc(x_710);
lean_dec(x_698);
x_711 = lean_ctor_get(x_699, 0);
lean_inc(x_711);
lean_dec(x_699);
x_1 = x_711;
x_3 = x_710;
goto _start;
}
}
else
{
uint8_t x_713; 
lean_dec(x_5);
lean_dec(x_2);
x_713 = !lean_is_exclusive(x_698);
if (x_713 == 0)
{
return x_698;
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_714 = lean_ctor_get(x_698, 0);
x_715 = lean_ctor_get(x_698, 1);
lean_inc(x_715);
lean_inc(x_714);
lean_dec(x_698);
x_716 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_716, 0, x_714);
lean_ctor_set(x_716, 1, x_715);
return x_716;
}
}
}
else
{
lean_object* x_717; 
x_717 = l_Lean_ConstantInfo_value_x3f(x_689);
lean_dec(x_689);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
lean_dec(x_691);
lean_dec(x_687);
lean_dec(x_682);
lean_dec(x_675);
x_718 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_719 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_719, 0, x_718);
x_720 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_720, 0, x_719);
x_721 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__9;
x_722 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_722, 0, x_721);
lean_ctor_set(x_722, 1, x_720);
x_723 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_724 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_724, 0, x_722);
lean_ctor_set(x_724, 1, x_723);
x_725 = lean_box(0);
x_726 = l_Lean_Meta_throwOther___rarg(x_724, x_725, x_2, x_695);
lean_dec(x_2);
return x_726;
}
else
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; 
lean_dec(x_5);
x_727 = lean_ctor_get(x_717, 0);
lean_inc(x_727);
lean_dec(x_717);
x_728 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_727);
lean_inc(x_2);
x_729 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_728, x_2, x_695);
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_771; lean_object* x_772; 
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_729, 1);
lean_inc(x_731);
lean_dec(x_729);
x_771 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__14;
lean_inc(x_2);
x_772 = l_Lean_Meta_forallTelescope___rarg(x_691, x_771, x_2, x_731);
if (lean_obj_tag(x_772) == 0)
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; uint8_t x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_773 = lean_ctor_get(x_772, 0);
lean_inc(x_773);
x_774 = lean_ctor_get(x_772, 1);
lean_inc(x_774);
lean_dec(x_772);
lean_inc(x_687);
x_775 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_775, 0, x_687);
lean_ctor_set(x_775, 1, x_685);
lean_ctor_set(x_775, 2, x_773);
x_776 = lean_box(0);
x_777 = 0;
x_778 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_778, 0, x_775);
lean_ctor_set(x_778, 1, x_730);
lean_ctor_set(x_778, 2, x_776);
lean_ctor_set_uint8(x_778, sizeof(void*)*3, x_777);
x_779 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_779, 0, x_778);
x_780 = lean_ctor_get(x_774, 0);
lean_inc(x_780);
x_781 = l_Lean_Options_empty;
x_782 = l_Lean_Environment_addAndCompile(x_780, x_781, x_779);
lean_dec(x_779);
if (lean_obj_tag(x_782) == 0)
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; 
lean_dec(x_687);
lean_dec(x_682);
lean_dec(x_675);
x_783 = lean_ctor_get(x_782, 0);
lean_inc(x_783);
lean_dec(x_782);
x_784 = l_Lean_KernelException_toMessageData(x_783, x_781);
x_785 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_784);
x_786 = l_Lean_Format_pretty(x_785, x_781);
x_787 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_787, 0, x_786);
x_788 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_788, 0, x_787);
x_789 = lean_box(0);
x_790 = l_Lean_Meta_throwOther___rarg(x_788, x_789, x_2, x_774);
lean_dec(x_2);
x_791 = !lean_is_exclusive(x_790);
if (x_791 == 0)
{
return x_790;
}
else
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_792 = lean_ctor_get(x_790, 0);
x_793 = lean_ctor_get(x_790, 1);
lean_inc(x_793);
lean_inc(x_792);
lean_dec(x_790);
x_794 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_794, 0, x_792);
lean_ctor_set(x_794, 1, x_793);
return x_794;
}
}
else
{
lean_object* x_795; 
x_795 = lean_ctor_get(x_782, 0);
lean_inc(x_795);
lean_dec(x_782);
x_732 = x_795;
x_733 = x_774;
goto block_770;
}
}
else
{
uint8_t x_796; 
lean_dec(x_730);
lean_dec(x_687);
lean_dec(x_682);
lean_dec(x_675);
lean_dec(x_2);
x_796 = !lean_is_exclusive(x_772);
if (x_796 == 0)
{
return x_772;
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; 
x_797 = lean_ctor_get(x_772, 0);
x_798 = lean_ctor_get(x_772, 1);
lean_inc(x_798);
lean_inc(x_797);
lean_dec(x_772);
x_799 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_799, 0, x_797);
lean_ctor_set(x_799, 1, x_798);
return x_799;
}
}
block_770:
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; uint8_t x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_734 = lean_mk_syntax_ident(x_675);
x_735 = l_Lean_mkOptionalNode___closed__2;
x_736 = lean_array_push(x_735, x_734);
x_737 = l_Lean_nullKind;
x_738 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_738, 0, x_737);
lean_ctor_set(x_738, 1, x_736);
x_739 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
x_740 = 1;
x_741 = lean_box(0);
lean_inc(x_687);
x_742 = lean_add_attribute(x_732, x_687, x_739, x_738, x_740, x_741);
x_743 = lean_box(0);
x_744 = l_Lean_mkConst(x_687, x_743);
if (lean_obj_tag(x_742) == 0)
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; 
x_757 = lean_ctor_get(x_742, 0);
lean_inc(x_757);
lean_dec(x_742);
x_758 = l_Lean_Meta_setEnv(x_757, x_2, x_733);
x_759 = lean_ctor_get(x_758, 1);
lean_inc(x_759);
lean_dec(x_758);
x_745 = x_759;
goto block_756;
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; uint8_t x_766; 
lean_dec(x_744);
lean_dec(x_682);
x_760 = lean_ctor_get(x_742, 0);
lean_inc(x_760);
lean_dec(x_742);
x_761 = lean_io_error_to_string(x_760);
x_762 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_762, 0, x_761);
x_763 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_763, 0, x_762);
x_764 = lean_box(0);
x_765 = l_Lean_Meta_throwOther___rarg(x_763, x_764, x_2, x_733);
lean_dec(x_2);
x_766 = !lean_is_exclusive(x_765);
if (x_766 == 0)
{
return x_765;
}
else
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; 
x_767 = lean_ctor_get(x_765, 0);
x_768 = lean_ctor_get(x_765, 1);
lean_inc(x_768);
lean_inc(x_767);
lean_dec(x_765);
x_769 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_769, 0, x_767);
lean_ctor_set(x_769, 1, x_768);
return x_769;
}
}
block_756:
{
lean_object* x_746; 
lean_inc(x_2);
lean_inc(x_744);
x_746 = l_Lean_Meta_inferType(x_744, x_2, x_745);
if (lean_obj_tag(x_746) == 0)
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; 
x_747 = lean_ctor_get(x_746, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_746, 1);
lean_inc(x_748);
lean_dec(x_746);
x_749 = l_Lean_mkAppStx___closed__2;
x_750 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__13___boxed), 8, 4);
lean_closure_set(x_750, 0, x_692);
lean_closure_set(x_750, 1, x_749);
lean_closure_set(x_750, 2, x_682);
lean_closure_set(x_750, 3, x_744);
x_751 = l_Lean_Meta_forallTelescope___rarg(x_747, x_750, x_2, x_748);
return x_751;
}
else
{
uint8_t x_752; 
lean_dec(x_744);
lean_dec(x_682);
lean_dec(x_2);
x_752 = !lean_is_exclusive(x_746);
if (x_752 == 0)
{
return x_746;
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_753 = lean_ctor_get(x_746, 0);
x_754 = lean_ctor_get(x_746, 1);
lean_inc(x_754);
lean_inc(x_753);
lean_dec(x_746);
x_755 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_755, 0, x_753);
lean_ctor_set(x_755, 1, x_754);
return x_755;
}
}
}
}
}
else
{
uint8_t x_800; 
lean_dec(x_691);
lean_dec(x_687);
lean_dec(x_682);
lean_dec(x_675);
lean_dec(x_2);
x_800 = !lean_is_exclusive(x_729);
if (x_800 == 0)
{
return x_729;
}
else
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; 
x_801 = lean_ctor_get(x_729, 0);
x_802 = lean_ctor_get(x_729, 1);
lean_inc(x_802);
lean_inc(x_801);
lean_dec(x_729);
x_803 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_803, 0, x_801);
lean_ctor_set(x_803, 1, x_802);
return x_803;
}
}
}
}
}
else
{
uint8_t x_804; 
lean_dec(x_691);
lean_dec(x_689);
lean_dec(x_687);
lean_dec(x_682);
lean_dec(x_675);
lean_dec(x_5);
lean_dec(x_2);
x_804 = !lean_is_exclusive(x_693);
if (x_804 == 0)
{
return x_693;
}
else
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_805 = lean_ctor_get(x_693, 0);
x_806 = lean_ctor_get(x_693, 1);
lean_inc(x_806);
lean_inc(x_805);
lean_dec(x_693);
x_807 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_807, 0, x_805);
lean_ctor_set(x_807, 1, x_806);
return x_807;
}
}
}
else
{
uint8_t x_808; 
lean_dec(x_687);
lean_dec(x_682);
lean_dec(x_675);
lean_dec(x_5);
lean_dec(x_2);
x_808 = !lean_is_exclusive(x_688);
if (x_808 == 0)
{
return x_688;
}
else
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_809 = lean_ctor_get(x_688, 0);
x_810 = lean_ctor_get(x_688, 1);
lean_inc(x_810);
lean_inc(x_809);
lean_dec(x_688);
x_811 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_811, 0, x_809);
lean_ctor_set(x_811, 1, x_810);
return x_811;
}
}
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; 
lean_dec(x_675);
lean_dec(x_5);
x_812 = lean_ctor_get(x_685, 0);
lean_inc(x_812);
lean_dec(x_685);
x_813 = lean_box(0);
x_814 = l_Lean_mkConst(x_812, x_813);
lean_inc(x_2);
lean_inc(x_814);
x_815 = l_Lean_Meta_inferType(x_814, x_2, x_662);
if (lean_obj_tag(x_815) == 0)
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_816 = lean_ctor_get(x_815, 0);
lean_inc(x_816);
x_817 = lean_ctor_get(x_815, 1);
lean_inc(x_817);
lean_dec(x_815);
x_818 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__15___boxed), 6, 2);
lean_closure_set(x_818, 0, x_682);
lean_closure_set(x_818, 1, x_814);
x_819 = l_Lean_Meta_forallTelescope___rarg(x_816, x_818, x_2, x_817);
return x_819;
}
else
{
uint8_t x_820; 
lean_dec(x_814);
lean_dec(x_682);
lean_dec(x_2);
x_820 = !lean_is_exclusive(x_815);
if (x_820 == 0)
{
return x_815;
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_821 = lean_ctor_get(x_815, 0);
x_822 = lean_ctor_get(x_815, 1);
lean_inc(x_822);
lean_inc(x_821);
lean_dec(x_815);
x_823 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_823, 0, x_821);
lean_ctor_set(x_823, 1, x_822);
return x_823;
}
}
}
}
else
{
lean_object* x_824; 
lean_dec(x_663);
x_824 = lean_box(0);
x_664 = x_824;
goto block_674;
}
block_674:
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; 
lean_dec(x_664);
x_665 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_666 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_666, 0, x_665);
x_667 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_667, 0, x_666);
x_668 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_669 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_669, 0, x_668);
lean_ctor_set(x_669, 1, x_667);
x_670 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_671 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_671, 0, x_669);
lean_ctor_set(x_671, 1, x_670);
x_672 = lean_box(0);
x_673 = l_Lean_Meta_throwOther___rarg(x_671, x_672, x_2, x_662);
lean_dec(x_2);
return x_673;
}
}
case 6:
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_825 = lean_ctor_get(x_4, 1);
lean_inc(x_825);
lean_dec(x_4);
x_826 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__15;
x_827 = l_Lean_Meta_lambdaTelescope___rarg(x_5, x_826, x_2, x_825);
return x_827;
}
case 7:
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; 
x_828 = lean_ctor_get(x_4, 1);
lean_inc(x_828);
lean_dec(x_4);
x_829 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_829) == 4)
{
lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_841 = lean_ctor_get(x_829, 0);
lean_inc(x_841);
lean_dec(x_829);
x_842 = lean_unsigned_to_nat(0u);
x_843 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_842);
x_844 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_843);
x_845 = lean_mk_array(x_843, x_844);
x_846 = lean_unsigned_to_nat(1u);
x_847 = lean_nat_sub(x_843, x_846);
lean_dec(x_843);
lean_inc(x_5);
x_848 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_845, x_847);
x_849 = lean_ctor_get(x_828, 0);
lean_inc(x_849);
x_850 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_851 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_850, x_849, x_841);
lean_dec(x_849);
if (lean_obj_tag(x_851) == 0)
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; 
x_852 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_853 = l_Lean_Name_append___main(x_841, x_852);
lean_inc(x_841);
x_854 = l_Lean_Meta_getConstInfo(x_841, x_2, x_828);
if (lean_obj_tag(x_854) == 0)
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; 
x_855 = lean_ctor_get(x_854, 0);
lean_inc(x_855);
x_856 = lean_ctor_get(x_854, 1);
lean_inc(x_856);
lean_dec(x_854);
x_857 = l_Lean_ConstantInfo_type(x_855);
x_858 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_857);
x_859 = l_Lean_Meta_forallTelescope___rarg(x_857, x_858, x_2, x_856);
if (lean_obj_tag(x_859) == 0)
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; uint8_t x_863; 
x_860 = lean_ctor_get(x_859, 0);
lean_inc(x_860);
x_861 = lean_ctor_get(x_859, 1);
lean_inc(x_861);
lean_dec(x_859);
x_862 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_863 = l_Lean_Expr_isConstOf(x_860, x_862);
lean_dec(x_860);
if (x_863 == 0)
{
lean_object* x_864; 
lean_dec(x_857);
lean_dec(x_855);
lean_dec(x_853);
lean_dec(x_848);
lean_dec(x_841);
lean_inc(x_2);
lean_inc(x_5);
x_864 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_861);
if (lean_obj_tag(x_864) == 0)
{
lean_object* x_865; 
x_865 = lean_ctor_get(x_864, 0);
lean_inc(x_865);
if (lean_obj_tag(x_865) == 0)
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_866 = lean_ctor_get(x_864, 1);
lean_inc(x_866);
lean_dec(x_864);
x_867 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_868 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_868, 0, x_867);
x_869 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_869, 0, x_868);
x_870 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_871 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_871, 0, x_870);
lean_ctor_set(x_871, 1, x_869);
x_872 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_873 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_873, 0, x_871);
lean_ctor_set(x_873, 1, x_872);
x_874 = lean_box(0);
x_875 = l_Lean_Meta_throwOther___rarg(x_873, x_874, x_2, x_866);
lean_dec(x_2);
return x_875;
}
else
{
lean_object* x_876; lean_object* x_877; 
lean_dec(x_5);
x_876 = lean_ctor_get(x_864, 1);
lean_inc(x_876);
lean_dec(x_864);
x_877 = lean_ctor_get(x_865, 0);
lean_inc(x_877);
lean_dec(x_865);
x_1 = x_877;
x_3 = x_876;
goto _start;
}
}
else
{
uint8_t x_879; 
lean_dec(x_5);
lean_dec(x_2);
x_879 = !lean_is_exclusive(x_864);
if (x_879 == 0)
{
return x_864;
}
else
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; 
x_880 = lean_ctor_get(x_864, 0);
x_881 = lean_ctor_get(x_864, 1);
lean_inc(x_881);
lean_inc(x_880);
lean_dec(x_864);
x_882 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_882, 0, x_880);
lean_ctor_set(x_882, 1, x_881);
return x_882;
}
}
}
else
{
lean_object* x_883; 
x_883 = l_Lean_ConstantInfo_value_x3f(x_855);
lean_dec(x_855);
if (lean_obj_tag(x_883) == 0)
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; 
lean_dec(x_857);
lean_dec(x_853);
lean_dec(x_848);
lean_dec(x_841);
x_884 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_885 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_885, 0, x_884);
x_886 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_886, 0, x_885);
x_887 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__9;
x_888 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_888, 0, x_887);
lean_ctor_set(x_888, 1, x_886);
x_889 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_890 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_890, 0, x_888);
lean_ctor_set(x_890, 1, x_889);
x_891 = lean_box(0);
x_892 = l_Lean_Meta_throwOther___rarg(x_890, x_891, x_2, x_861);
lean_dec(x_2);
return x_892;
}
else
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; 
lean_dec(x_5);
x_893 = lean_ctor_get(x_883, 0);
lean_inc(x_893);
lean_dec(x_883);
x_894 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_893);
lean_inc(x_2);
x_895 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_894, x_2, x_861);
if (lean_obj_tag(x_895) == 0)
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_937; lean_object* x_938; 
x_896 = lean_ctor_get(x_895, 0);
lean_inc(x_896);
x_897 = lean_ctor_get(x_895, 1);
lean_inc(x_897);
lean_dec(x_895);
x_937 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__16;
lean_inc(x_2);
x_938 = l_Lean_Meta_forallTelescope___rarg(x_857, x_937, x_2, x_897);
if (lean_obj_tag(x_938) == 0)
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; uint8_t x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; 
x_939 = lean_ctor_get(x_938, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_938, 1);
lean_inc(x_940);
lean_dec(x_938);
lean_inc(x_853);
x_941 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_941, 0, x_853);
lean_ctor_set(x_941, 1, x_851);
lean_ctor_set(x_941, 2, x_939);
x_942 = lean_box(0);
x_943 = 0;
x_944 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_944, 0, x_941);
lean_ctor_set(x_944, 1, x_896);
lean_ctor_set(x_944, 2, x_942);
lean_ctor_set_uint8(x_944, sizeof(void*)*3, x_943);
x_945 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_945, 0, x_944);
x_946 = lean_ctor_get(x_940, 0);
lean_inc(x_946);
x_947 = l_Lean_Options_empty;
x_948 = l_Lean_Environment_addAndCompile(x_946, x_947, x_945);
lean_dec(x_945);
if (lean_obj_tag(x_948) == 0)
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; uint8_t x_957; 
lean_dec(x_853);
lean_dec(x_848);
lean_dec(x_841);
x_949 = lean_ctor_get(x_948, 0);
lean_inc(x_949);
lean_dec(x_948);
x_950 = l_Lean_KernelException_toMessageData(x_949, x_947);
x_951 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_950);
x_952 = l_Lean_Format_pretty(x_951, x_947);
x_953 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_953, 0, x_952);
x_954 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_954, 0, x_953);
x_955 = lean_box(0);
x_956 = l_Lean_Meta_throwOther___rarg(x_954, x_955, x_2, x_940);
lean_dec(x_2);
x_957 = !lean_is_exclusive(x_956);
if (x_957 == 0)
{
return x_956;
}
else
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; 
x_958 = lean_ctor_get(x_956, 0);
x_959 = lean_ctor_get(x_956, 1);
lean_inc(x_959);
lean_inc(x_958);
lean_dec(x_956);
x_960 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_960, 0, x_958);
lean_ctor_set(x_960, 1, x_959);
return x_960;
}
}
else
{
lean_object* x_961; 
x_961 = lean_ctor_get(x_948, 0);
lean_inc(x_961);
lean_dec(x_948);
x_898 = x_961;
x_899 = x_940;
goto block_936;
}
}
else
{
uint8_t x_962; 
lean_dec(x_896);
lean_dec(x_853);
lean_dec(x_848);
lean_dec(x_841);
lean_dec(x_2);
x_962 = !lean_is_exclusive(x_938);
if (x_962 == 0)
{
return x_938;
}
else
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; 
x_963 = lean_ctor_get(x_938, 0);
x_964 = lean_ctor_get(x_938, 1);
lean_inc(x_964);
lean_inc(x_963);
lean_dec(x_938);
x_965 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_965, 0, x_963);
lean_ctor_set(x_965, 1, x_964);
return x_965;
}
}
block_936:
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; uint8_t x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; 
x_900 = lean_mk_syntax_ident(x_841);
x_901 = l_Lean_mkOptionalNode___closed__2;
x_902 = lean_array_push(x_901, x_900);
x_903 = l_Lean_nullKind;
x_904 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_904, 0, x_903);
lean_ctor_set(x_904, 1, x_902);
x_905 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
x_906 = 1;
x_907 = lean_box(0);
lean_inc(x_853);
x_908 = lean_add_attribute(x_898, x_853, x_905, x_904, x_906, x_907);
x_909 = lean_box(0);
x_910 = l_Lean_mkConst(x_853, x_909);
if (lean_obj_tag(x_908) == 0)
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; 
x_923 = lean_ctor_get(x_908, 0);
lean_inc(x_923);
lean_dec(x_908);
x_924 = l_Lean_Meta_setEnv(x_923, x_2, x_899);
x_925 = lean_ctor_get(x_924, 1);
lean_inc(x_925);
lean_dec(x_924);
x_911 = x_925;
goto block_922;
}
else
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; uint8_t x_932; 
lean_dec(x_910);
lean_dec(x_848);
x_926 = lean_ctor_get(x_908, 0);
lean_inc(x_926);
lean_dec(x_908);
x_927 = lean_io_error_to_string(x_926);
x_928 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_928, 0, x_927);
x_929 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_929, 0, x_928);
x_930 = lean_box(0);
x_931 = l_Lean_Meta_throwOther___rarg(x_929, x_930, x_2, x_899);
lean_dec(x_2);
x_932 = !lean_is_exclusive(x_931);
if (x_932 == 0)
{
return x_931;
}
else
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; 
x_933 = lean_ctor_get(x_931, 0);
x_934 = lean_ctor_get(x_931, 1);
lean_inc(x_934);
lean_inc(x_933);
lean_dec(x_931);
x_935 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_935, 0, x_933);
lean_ctor_set(x_935, 1, x_934);
return x_935;
}
}
block_922:
{
lean_object* x_912; 
lean_inc(x_2);
lean_inc(x_910);
x_912 = l_Lean_Meta_inferType(x_910, x_2, x_911);
if (lean_obj_tag(x_912) == 0)
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; 
x_913 = lean_ctor_get(x_912, 0);
lean_inc(x_913);
x_914 = lean_ctor_get(x_912, 1);
lean_inc(x_914);
lean_dec(x_912);
x_915 = l_Lean_mkAppStx___closed__2;
x_916 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__17___boxed), 8, 4);
lean_closure_set(x_916, 0, x_858);
lean_closure_set(x_916, 1, x_915);
lean_closure_set(x_916, 2, x_848);
lean_closure_set(x_916, 3, x_910);
x_917 = l_Lean_Meta_forallTelescope___rarg(x_913, x_916, x_2, x_914);
return x_917;
}
else
{
uint8_t x_918; 
lean_dec(x_910);
lean_dec(x_848);
lean_dec(x_2);
x_918 = !lean_is_exclusive(x_912);
if (x_918 == 0)
{
return x_912;
}
else
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; 
x_919 = lean_ctor_get(x_912, 0);
x_920 = lean_ctor_get(x_912, 1);
lean_inc(x_920);
lean_inc(x_919);
lean_dec(x_912);
x_921 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_921, 0, x_919);
lean_ctor_set(x_921, 1, x_920);
return x_921;
}
}
}
}
}
else
{
uint8_t x_966; 
lean_dec(x_857);
lean_dec(x_853);
lean_dec(x_848);
lean_dec(x_841);
lean_dec(x_2);
x_966 = !lean_is_exclusive(x_895);
if (x_966 == 0)
{
return x_895;
}
else
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; 
x_967 = lean_ctor_get(x_895, 0);
x_968 = lean_ctor_get(x_895, 1);
lean_inc(x_968);
lean_inc(x_967);
lean_dec(x_895);
x_969 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_969, 0, x_967);
lean_ctor_set(x_969, 1, x_968);
return x_969;
}
}
}
}
}
else
{
uint8_t x_970; 
lean_dec(x_857);
lean_dec(x_855);
lean_dec(x_853);
lean_dec(x_848);
lean_dec(x_841);
lean_dec(x_5);
lean_dec(x_2);
x_970 = !lean_is_exclusive(x_859);
if (x_970 == 0)
{
return x_859;
}
else
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; 
x_971 = lean_ctor_get(x_859, 0);
x_972 = lean_ctor_get(x_859, 1);
lean_inc(x_972);
lean_inc(x_971);
lean_dec(x_859);
x_973 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_973, 0, x_971);
lean_ctor_set(x_973, 1, x_972);
return x_973;
}
}
}
else
{
uint8_t x_974; 
lean_dec(x_853);
lean_dec(x_848);
lean_dec(x_841);
lean_dec(x_5);
lean_dec(x_2);
x_974 = !lean_is_exclusive(x_854);
if (x_974 == 0)
{
return x_854;
}
else
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; 
x_975 = lean_ctor_get(x_854, 0);
x_976 = lean_ctor_get(x_854, 1);
lean_inc(x_976);
lean_inc(x_975);
lean_dec(x_854);
x_977 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_977, 0, x_975);
lean_ctor_set(x_977, 1, x_976);
return x_977;
}
}
}
else
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; 
lean_dec(x_841);
lean_dec(x_5);
x_978 = lean_ctor_get(x_851, 0);
lean_inc(x_978);
lean_dec(x_851);
x_979 = lean_box(0);
x_980 = l_Lean_mkConst(x_978, x_979);
lean_inc(x_2);
lean_inc(x_980);
x_981 = l_Lean_Meta_inferType(x_980, x_2, x_828);
if (lean_obj_tag(x_981) == 0)
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; 
x_982 = lean_ctor_get(x_981, 0);
lean_inc(x_982);
x_983 = lean_ctor_get(x_981, 1);
lean_inc(x_983);
lean_dec(x_981);
x_984 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__19___boxed), 6, 2);
lean_closure_set(x_984, 0, x_848);
lean_closure_set(x_984, 1, x_980);
x_985 = l_Lean_Meta_forallTelescope___rarg(x_982, x_984, x_2, x_983);
return x_985;
}
else
{
uint8_t x_986; 
lean_dec(x_980);
lean_dec(x_848);
lean_dec(x_2);
x_986 = !lean_is_exclusive(x_981);
if (x_986 == 0)
{
return x_981;
}
else
{
lean_object* x_987; lean_object* x_988; lean_object* x_989; 
x_987 = lean_ctor_get(x_981, 0);
x_988 = lean_ctor_get(x_981, 1);
lean_inc(x_988);
lean_inc(x_987);
lean_dec(x_981);
x_989 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_989, 0, x_987);
lean_ctor_set(x_989, 1, x_988);
return x_989;
}
}
}
}
else
{
lean_object* x_990; 
lean_dec(x_829);
x_990 = lean_box(0);
x_830 = x_990;
goto block_840;
}
block_840:
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; 
lean_dec(x_830);
x_831 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_832 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_832, 0, x_831);
x_833 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_833, 0, x_832);
x_834 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_835 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_835, 0, x_834);
lean_ctor_set(x_835, 1, x_833);
x_836 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_837 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_837, 0, x_835);
lean_ctor_set(x_837, 1, x_836);
x_838 = lean_box(0);
x_839 = l_Lean_Meta_throwOther___rarg(x_837, x_838, x_2, x_828);
lean_dec(x_2);
return x_839;
}
}
case 8:
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; 
x_991 = lean_ctor_get(x_4, 1);
lean_inc(x_991);
lean_dec(x_4);
x_992 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_992) == 4)
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; 
x_1004 = lean_ctor_get(x_992, 0);
lean_inc(x_1004);
lean_dec(x_992);
x_1005 = lean_unsigned_to_nat(0u);
x_1006 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_1005);
x_1007 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1006);
x_1008 = lean_mk_array(x_1006, x_1007);
x_1009 = lean_unsigned_to_nat(1u);
x_1010 = lean_nat_sub(x_1006, x_1009);
lean_dec(x_1006);
lean_inc(x_5);
x_1011 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_1008, x_1010);
x_1012 = lean_ctor_get(x_991, 0);
lean_inc(x_1012);
x_1013 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_1014 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_1013, x_1012, x_1004);
lean_dec(x_1012);
if (lean_obj_tag(x_1014) == 0)
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; 
x_1015 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_1016 = l_Lean_Name_append___main(x_1004, x_1015);
lean_inc(x_1004);
x_1017 = l_Lean_Meta_getConstInfo(x_1004, x_2, x_991);
if (lean_obj_tag(x_1017) == 0)
{
lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; 
x_1018 = lean_ctor_get(x_1017, 0);
lean_inc(x_1018);
x_1019 = lean_ctor_get(x_1017, 1);
lean_inc(x_1019);
lean_dec(x_1017);
x_1020 = l_Lean_ConstantInfo_type(x_1018);
x_1021 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_1020);
x_1022 = l_Lean_Meta_forallTelescope___rarg(x_1020, x_1021, x_2, x_1019);
if (lean_obj_tag(x_1022) == 0)
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; uint8_t x_1026; 
x_1023 = lean_ctor_get(x_1022, 0);
lean_inc(x_1023);
x_1024 = lean_ctor_get(x_1022, 1);
lean_inc(x_1024);
lean_dec(x_1022);
x_1025 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_1026 = l_Lean_Expr_isConstOf(x_1023, x_1025);
lean_dec(x_1023);
if (x_1026 == 0)
{
lean_object* x_1027; 
lean_dec(x_1020);
lean_dec(x_1018);
lean_dec(x_1016);
lean_dec(x_1011);
lean_dec(x_1004);
lean_inc(x_2);
lean_inc(x_5);
x_1027 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_1024);
if (lean_obj_tag(x_1027) == 0)
{
lean_object* x_1028; 
x_1028 = lean_ctor_get(x_1027, 0);
lean_inc(x_1028);
if (lean_obj_tag(x_1028) == 0)
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
x_1029 = lean_ctor_get(x_1027, 1);
lean_inc(x_1029);
lean_dec(x_1027);
x_1030 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1031 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1031, 0, x_1030);
x_1032 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1032, 0, x_1031);
x_1033 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_1034 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1034, 0, x_1033);
lean_ctor_set(x_1034, 1, x_1032);
x_1035 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_1036 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1036, 0, x_1034);
lean_ctor_set(x_1036, 1, x_1035);
x_1037 = lean_box(0);
x_1038 = l_Lean_Meta_throwOther___rarg(x_1036, x_1037, x_2, x_1029);
lean_dec(x_2);
return x_1038;
}
else
{
lean_object* x_1039; lean_object* x_1040; 
lean_dec(x_5);
x_1039 = lean_ctor_get(x_1027, 1);
lean_inc(x_1039);
lean_dec(x_1027);
x_1040 = lean_ctor_get(x_1028, 0);
lean_inc(x_1040);
lean_dec(x_1028);
x_1 = x_1040;
x_3 = x_1039;
goto _start;
}
}
else
{
uint8_t x_1042; 
lean_dec(x_5);
lean_dec(x_2);
x_1042 = !lean_is_exclusive(x_1027);
if (x_1042 == 0)
{
return x_1027;
}
else
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; 
x_1043 = lean_ctor_get(x_1027, 0);
x_1044 = lean_ctor_get(x_1027, 1);
lean_inc(x_1044);
lean_inc(x_1043);
lean_dec(x_1027);
x_1045 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1045, 0, x_1043);
lean_ctor_set(x_1045, 1, x_1044);
return x_1045;
}
}
}
else
{
lean_object* x_1046; 
x_1046 = l_Lean_ConstantInfo_value_x3f(x_1018);
lean_dec(x_1018);
if (lean_obj_tag(x_1046) == 0)
{
lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
lean_dec(x_1020);
lean_dec(x_1016);
lean_dec(x_1011);
lean_dec(x_1004);
x_1047 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1048 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1048, 0, x_1047);
x_1049 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1049, 0, x_1048);
x_1050 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__9;
x_1051 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1051, 0, x_1050);
lean_ctor_set(x_1051, 1, x_1049);
x_1052 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_1053 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1053, 0, x_1051);
lean_ctor_set(x_1053, 1, x_1052);
x_1054 = lean_box(0);
x_1055 = l_Lean_Meta_throwOther___rarg(x_1053, x_1054, x_2, x_1024);
lean_dec(x_2);
return x_1055;
}
else
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; 
lean_dec(x_5);
x_1056 = lean_ctor_get(x_1046, 0);
lean_inc(x_1056);
lean_dec(x_1046);
x_1057 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_1056);
lean_inc(x_2);
x_1058 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_1057, x_2, x_1024);
if (lean_obj_tag(x_1058) == 0)
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1100; lean_object* x_1101; 
x_1059 = lean_ctor_get(x_1058, 0);
lean_inc(x_1059);
x_1060 = lean_ctor_get(x_1058, 1);
lean_inc(x_1060);
lean_dec(x_1058);
x_1100 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__17;
lean_inc(x_2);
x_1101 = l_Lean_Meta_forallTelescope___rarg(x_1020, x_1100, x_2, x_1060);
if (lean_obj_tag(x_1101) == 0)
{
lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; uint8_t x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; 
x_1102 = lean_ctor_get(x_1101, 0);
lean_inc(x_1102);
x_1103 = lean_ctor_get(x_1101, 1);
lean_inc(x_1103);
lean_dec(x_1101);
lean_inc(x_1016);
x_1104 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1104, 0, x_1016);
lean_ctor_set(x_1104, 1, x_1014);
lean_ctor_set(x_1104, 2, x_1102);
x_1105 = lean_box(0);
x_1106 = 0;
x_1107 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1107, 0, x_1104);
lean_ctor_set(x_1107, 1, x_1059);
lean_ctor_set(x_1107, 2, x_1105);
lean_ctor_set_uint8(x_1107, sizeof(void*)*3, x_1106);
x_1108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1108, 0, x_1107);
x_1109 = lean_ctor_get(x_1103, 0);
lean_inc(x_1109);
x_1110 = l_Lean_Options_empty;
x_1111 = l_Lean_Environment_addAndCompile(x_1109, x_1110, x_1108);
lean_dec(x_1108);
if (lean_obj_tag(x_1111) == 0)
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; uint8_t x_1120; 
lean_dec(x_1016);
lean_dec(x_1011);
lean_dec(x_1004);
x_1112 = lean_ctor_get(x_1111, 0);
lean_inc(x_1112);
lean_dec(x_1111);
x_1113 = l_Lean_KernelException_toMessageData(x_1112, x_1110);
x_1114 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1113);
x_1115 = l_Lean_Format_pretty(x_1114, x_1110);
x_1116 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1116, 0, x_1115);
x_1117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1117, 0, x_1116);
x_1118 = lean_box(0);
x_1119 = l_Lean_Meta_throwOther___rarg(x_1117, x_1118, x_2, x_1103);
lean_dec(x_2);
x_1120 = !lean_is_exclusive(x_1119);
if (x_1120 == 0)
{
return x_1119;
}
else
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; 
x_1121 = lean_ctor_get(x_1119, 0);
x_1122 = lean_ctor_get(x_1119, 1);
lean_inc(x_1122);
lean_inc(x_1121);
lean_dec(x_1119);
x_1123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1123, 0, x_1121);
lean_ctor_set(x_1123, 1, x_1122);
return x_1123;
}
}
else
{
lean_object* x_1124; 
x_1124 = lean_ctor_get(x_1111, 0);
lean_inc(x_1124);
lean_dec(x_1111);
x_1061 = x_1124;
x_1062 = x_1103;
goto block_1099;
}
}
else
{
uint8_t x_1125; 
lean_dec(x_1059);
lean_dec(x_1016);
lean_dec(x_1011);
lean_dec(x_1004);
lean_dec(x_2);
x_1125 = !lean_is_exclusive(x_1101);
if (x_1125 == 0)
{
return x_1101;
}
else
{
lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; 
x_1126 = lean_ctor_get(x_1101, 0);
x_1127 = lean_ctor_get(x_1101, 1);
lean_inc(x_1127);
lean_inc(x_1126);
lean_dec(x_1101);
x_1128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1128, 0, x_1126);
lean_ctor_set(x_1128, 1, x_1127);
return x_1128;
}
}
block_1099:
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; uint8_t x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; 
x_1063 = lean_mk_syntax_ident(x_1004);
x_1064 = l_Lean_mkOptionalNode___closed__2;
x_1065 = lean_array_push(x_1064, x_1063);
x_1066 = l_Lean_nullKind;
x_1067 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1067, 0, x_1066);
lean_ctor_set(x_1067, 1, x_1065);
x_1068 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
x_1069 = 1;
x_1070 = lean_box(0);
lean_inc(x_1016);
x_1071 = lean_add_attribute(x_1061, x_1016, x_1068, x_1067, x_1069, x_1070);
x_1072 = lean_box(0);
x_1073 = l_Lean_mkConst(x_1016, x_1072);
if (lean_obj_tag(x_1071) == 0)
{
lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; 
x_1086 = lean_ctor_get(x_1071, 0);
lean_inc(x_1086);
lean_dec(x_1071);
x_1087 = l_Lean_Meta_setEnv(x_1086, x_2, x_1062);
x_1088 = lean_ctor_get(x_1087, 1);
lean_inc(x_1088);
lean_dec(x_1087);
x_1074 = x_1088;
goto block_1085;
}
else
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; uint8_t x_1095; 
lean_dec(x_1073);
lean_dec(x_1011);
x_1089 = lean_ctor_get(x_1071, 0);
lean_inc(x_1089);
lean_dec(x_1071);
x_1090 = lean_io_error_to_string(x_1089);
x_1091 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1091, 0, x_1090);
x_1092 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1092, 0, x_1091);
x_1093 = lean_box(0);
x_1094 = l_Lean_Meta_throwOther___rarg(x_1092, x_1093, x_2, x_1062);
lean_dec(x_2);
x_1095 = !lean_is_exclusive(x_1094);
if (x_1095 == 0)
{
return x_1094;
}
else
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; 
x_1096 = lean_ctor_get(x_1094, 0);
x_1097 = lean_ctor_get(x_1094, 1);
lean_inc(x_1097);
lean_inc(x_1096);
lean_dec(x_1094);
x_1098 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1098, 0, x_1096);
lean_ctor_set(x_1098, 1, x_1097);
return x_1098;
}
}
block_1085:
{
lean_object* x_1075; 
lean_inc(x_2);
lean_inc(x_1073);
x_1075 = l_Lean_Meta_inferType(x_1073, x_2, x_1074);
if (lean_obj_tag(x_1075) == 0)
{
lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; 
x_1076 = lean_ctor_get(x_1075, 0);
lean_inc(x_1076);
x_1077 = lean_ctor_get(x_1075, 1);
lean_inc(x_1077);
lean_dec(x_1075);
x_1078 = l_Lean_mkAppStx___closed__2;
x_1079 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__20___boxed), 8, 4);
lean_closure_set(x_1079, 0, x_1021);
lean_closure_set(x_1079, 1, x_1078);
lean_closure_set(x_1079, 2, x_1011);
lean_closure_set(x_1079, 3, x_1073);
x_1080 = l_Lean_Meta_forallTelescope___rarg(x_1076, x_1079, x_2, x_1077);
return x_1080;
}
else
{
uint8_t x_1081; 
lean_dec(x_1073);
lean_dec(x_1011);
lean_dec(x_2);
x_1081 = !lean_is_exclusive(x_1075);
if (x_1081 == 0)
{
return x_1075;
}
else
{
lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; 
x_1082 = lean_ctor_get(x_1075, 0);
x_1083 = lean_ctor_get(x_1075, 1);
lean_inc(x_1083);
lean_inc(x_1082);
lean_dec(x_1075);
x_1084 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1084, 0, x_1082);
lean_ctor_set(x_1084, 1, x_1083);
return x_1084;
}
}
}
}
}
else
{
uint8_t x_1129; 
lean_dec(x_1020);
lean_dec(x_1016);
lean_dec(x_1011);
lean_dec(x_1004);
lean_dec(x_2);
x_1129 = !lean_is_exclusive(x_1058);
if (x_1129 == 0)
{
return x_1058;
}
else
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
x_1130 = lean_ctor_get(x_1058, 0);
x_1131 = lean_ctor_get(x_1058, 1);
lean_inc(x_1131);
lean_inc(x_1130);
lean_dec(x_1058);
x_1132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1132, 0, x_1130);
lean_ctor_set(x_1132, 1, x_1131);
return x_1132;
}
}
}
}
}
else
{
uint8_t x_1133; 
lean_dec(x_1020);
lean_dec(x_1018);
lean_dec(x_1016);
lean_dec(x_1011);
lean_dec(x_1004);
lean_dec(x_5);
lean_dec(x_2);
x_1133 = !lean_is_exclusive(x_1022);
if (x_1133 == 0)
{
return x_1022;
}
else
{
lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; 
x_1134 = lean_ctor_get(x_1022, 0);
x_1135 = lean_ctor_get(x_1022, 1);
lean_inc(x_1135);
lean_inc(x_1134);
lean_dec(x_1022);
x_1136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1136, 0, x_1134);
lean_ctor_set(x_1136, 1, x_1135);
return x_1136;
}
}
}
else
{
uint8_t x_1137; 
lean_dec(x_1016);
lean_dec(x_1011);
lean_dec(x_1004);
lean_dec(x_5);
lean_dec(x_2);
x_1137 = !lean_is_exclusive(x_1017);
if (x_1137 == 0)
{
return x_1017;
}
else
{
lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
x_1138 = lean_ctor_get(x_1017, 0);
x_1139 = lean_ctor_get(x_1017, 1);
lean_inc(x_1139);
lean_inc(x_1138);
lean_dec(x_1017);
x_1140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1140, 0, x_1138);
lean_ctor_set(x_1140, 1, x_1139);
return x_1140;
}
}
}
else
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; 
lean_dec(x_1004);
lean_dec(x_5);
x_1141 = lean_ctor_get(x_1014, 0);
lean_inc(x_1141);
lean_dec(x_1014);
x_1142 = lean_box(0);
x_1143 = l_Lean_mkConst(x_1141, x_1142);
lean_inc(x_2);
lean_inc(x_1143);
x_1144 = l_Lean_Meta_inferType(x_1143, x_2, x_991);
if (lean_obj_tag(x_1144) == 0)
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; 
x_1145 = lean_ctor_get(x_1144, 0);
lean_inc(x_1145);
x_1146 = lean_ctor_get(x_1144, 1);
lean_inc(x_1146);
lean_dec(x_1144);
x_1147 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__22___boxed), 6, 2);
lean_closure_set(x_1147, 0, x_1011);
lean_closure_set(x_1147, 1, x_1143);
x_1148 = l_Lean_Meta_forallTelescope___rarg(x_1145, x_1147, x_2, x_1146);
return x_1148;
}
else
{
uint8_t x_1149; 
lean_dec(x_1143);
lean_dec(x_1011);
lean_dec(x_2);
x_1149 = !lean_is_exclusive(x_1144);
if (x_1149 == 0)
{
return x_1144;
}
else
{
lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; 
x_1150 = lean_ctor_get(x_1144, 0);
x_1151 = lean_ctor_get(x_1144, 1);
lean_inc(x_1151);
lean_inc(x_1150);
lean_dec(x_1144);
x_1152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1152, 0, x_1150);
lean_ctor_set(x_1152, 1, x_1151);
return x_1152;
}
}
}
}
else
{
lean_object* x_1153; 
lean_dec(x_992);
x_1153 = lean_box(0);
x_993 = x_1153;
goto block_1003;
}
block_1003:
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
lean_dec(x_993);
x_994 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_995 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_995, 0, x_994);
x_996 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_996, 0, x_995);
x_997 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_998 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_998, 0, x_997);
lean_ctor_set(x_998, 1, x_996);
x_999 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_1000 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1000, 0, x_998);
lean_ctor_set(x_1000, 1, x_999);
x_1001 = lean_box(0);
x_1002 = l_Lean_Meta_throwOther___rarg(x_1000, x_1001, x_2, x_991);
lean_dec(x_2);
return x_1002;
}
}
case 9:
{
lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; 
x_1154 = lean_ctor_get(x_4, 1);
lean_inc(x_1154);
lean_dec(x_4);
x_1155 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_1155) == 4)
{
lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; 
x_1167 = lean_ctor_get(x_1155, 0);
lean_inc(x_1167);
lean_dec(x_1155);
x_1168 = lean_unsigned_to_nat(0u);
x_1169 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_1168);
x_1170 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1169);
x_1171 = lean_mk_array(x_1169, x_1170);
x_1172 = lean_unsigned_to_nat(1u);
x_1173 = lean_nat_sub(x_1169, x_1172);
lean_dec(x_1169);
lean_inc(x_5);
x_1174 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_1171, x_1173);
x_1175 = lean_ctor_get(x_1154, 0);
lean_inc(x_1175);
x_1176 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_1177 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_1176, x_1175, x_1167);
lean_dec(x_1175);
if (lean_obj_tag(x_1177) == 0)
{
lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; 
x_1178 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_1179 = l_Lean_Name_append___main(x_1167, x_1178);
lean_inc(x_1167);
x_1180 = l_Lean_Meta_getConstInfo(x_1167, x_2, x_1154);
if (lean_obj_tag(x_1180) == 0)
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; 
x_1181 = lean_ctor_get(x_1180, 0);
lean_inc(x_1181);
x_1182 = lean_ctor_get(x_1180, 1);
lean_inc(x_1182);
lean_dec(x_1180);
x_1183 = l_Lean_ConstantInfo_type(x_1181);
x_1184 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_1183);
x_1185 = l_Lean_Meta_forallTelescope___rarg(x_1183, x_1184, x_2, x_1182);
if (lean_obj_tag(x_1185) == 0)
{
lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; uint8_t x_1189; 
x_1186 = lean_ctor_get(x_1185, 0);
lean_inc(x_1186);
x_1187 = lean_ctor_get(x_1185, 1);
lean_inc(x_1187);
lean_dec(x_1185);
x_1188 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_1189 = l_Lean_Expr_isConstOf(x_1186, x_1188);
lean_dec(x_1186);
if (x_1189 == 0)
{
lean_object* x_1190; 
lean_dec(x_1183);
lean_dec(x_1181);
lean_dec(x_1179);
lean_dec(x_1174);
lean_dec(x_1167);
lean_inc(x_2);
lean_inc(x_5);
x_1190 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_1187);
if (lean_obj_tag(x_1190) == 0)
{
lean_object* x_1191; 
x_1191 = lean_ctor_get(x_1190, 0);
lean_inc(x_1191);
if (lean_obj_tag(x_1191) == 0)
{
lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; 
x_1192 = lean_ctor_get(x_1190, 1);
lean_inc(x_1192);
lean_dec(x_1190);
x_1193 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1194 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1194, 0, x_1193);
x_1195 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1195, 0, x_1194);
x_1196 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_1197 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1197, 0, x_1196);
lean_ctor_set(x_1197, 1, x_1195);
x_1198 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_1199 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1199, 0, x_1197);
lean_ctor_set(x_1199, 1, x_1198);
x_1200 = lean_box(0);
x_1201 = l_Lean_Meta_throwOther___rarg(x_1199, x_1200, x_2, x_1192);
lean_dec(x_2);
return x_1201;
}
else
{
lean_object* x_1202; lean_object* x_1203; 
lean_dec(x_5);
x_1202 = lean_ctor_get(x_1190, 1);
lean_inc(x_1202);
lean_dec(x_1190);
x_1203 = lean_ctor_get(x_1191, 0);
lean_inc(x_1203);
lean_dec(x_1191);
x_1 = x_1203;
x_3 = x_1202;
goto _start;
}
}
else
{
uint8_t x_1205; 
lean_dec(x_5);
lean_dec(x_2);
x_1205 = !lean_is_exclusive(x_1190);
if (x_1205 == 0)
{
return x_1190;
}
else
{
lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; 
x_1206 = lean_ctor_get(x_1190, 0);
x_1207 = lean_ctor_get(x_1190, 1);
lean_inc(x_1207);
lean_inc(x_1206);
lean_dec(x_1190);
x_1208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1208, 0, x_1206);
lean_ctor_set(x_1208, 1, x_1207);
return x_1208;
}
}
}
else
{
lean_object* x_1209; 
x_1209 = l_Lean_ConstantInfo_value_x3f(x_1181);
lean_dec(x_1181);
if (lean_obj_tag(x_1209) == 0)
{
lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; 
lean_dec(x_1183);
lean_dec(x_1179);
lean_dec(x_1174);
lean_dec(x_1167);
x_1210 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1211 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1211, 0, x_1210);
x_1212 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1212, 0, x_1211);
x_1213 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__9;
x_1214 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1214, 0, x_1213);
lean_ctor_set(x_1214, 1, x_1212);
x_1215 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_1216 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1216, 0, x_1214);
lean_ctor_set(x_1216, 1, x_1215);
x_1217 = lean_box(0);
x_1218 = l_Lean_Meta_throwOther___rarg(x_1216, x_1217, x_2, x_1187);
lean_dec(x_2);
return x_1218;
}
else
{
lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; 
lean_dec(x_5);
x_1219 = lean_ctor_get(x_1209, 0);
lean_inc(x_1219);
lean_dec(x_1209);
x_1220 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_1219);
lean_inc(x_2);
x_1221 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_1220, x_2, x_1187);
if (lean_obj_tag(x_1221) == 0)
{
lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1263; lean_object* x_1264; 
x_1222 = lean_ctor_get(x_1221, 0);
lean_inc(x_1222);
x_1223 = lean_ctor_get(x_1221, 1);
lean_inc(x_1223);
lean_dec(x_1221);
x_1263 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__18;
lean_inc(x_2);
x_1264 = l_Lean_Meta_forallTelescope___rarg(x_1183, x_1263, x_2, x_1223);
if (lean_obj_tag(x_1264) == 0)
{
lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; uint8_t x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; 
x_1265 = lean_ctor_get(x_1264, 0);
lean_inc(x_1265);
x_1266 = lean_ctor_get(x_1264, 1);
lean_inc(x_1266);
lean_dec(x_1264);
lean_inc(x_1179);
x_1267 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1267, 0, x_1179);
lean_ctor_set(x_1267, 1, x_1177);
lean_ctor_set(x_1267, 2, x_1265);
x_1268 = lean_box(0);
x_1269 = 0;
x_1270 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1270, 0, x_1267);
lean_ctor_set(x_1270, 1, x_1222);
lean_ctor_set(x_1270, 2, x_1268);
lean_ctor_set_uint8(x_1270, sizeof(void*)*3, x_1269);
x_1271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1271, 0, x_1270);
x_1272 = lean_ctor_get(x_1266, 0);
lean_inc(x_1272);
x_1273 = l_Lean_Options_empty;
x_1274 = l_Lean_Environment_addAndCompile(x_1272, x_1273, x_1271);
lean_dec(x_1271);
if (lean_obj_tag(x_1274) == 0)
{
lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; uint8_t x_1283; 
lean_dec(x_1179);
lean_dec(x_1174);
lean_dec(x_1167);
x_1275 = lean_ctor_get(x_1274, 0);
lean_inc(x_1275);
lean_dec(x_1274);
x_1276 = l_Lean_KernelException_toMessageData(x_1275, x_1273);
x_1277 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1276);
x_1278 = l_Lean_Format_pretty(x_1277, x_1273);
x_1279 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1279, 0, x_1278);
x_1280 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1280, 0, x_1279);
x_1281 = lean_box(0);
x_1282 = l_Lean_Meta_throwOther___rarg(x_1280, x_1281, x_2, x_1266);
lean_dec(x_2);
x_1283 = !lean_is_exclusive(x_1282);
if (x_1283 == 0)
{
return x_1282;
}
else
{
lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; 
x_1284 = lean_ctor_get(x_1282, 0);
x_1285 = lean_ctor_get(x_1282, 1);
lean_inc(x_1285);
lean_inc(x_1284);
lean_dec(x_1282);
x_1286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1286, 0, x_1284);
lean_ctor_set(x_1286, 1, x_1285);
return x_1286;
}
}
else
{
lean_object* x_1287; 
x_1287 = lean_ctor_get(x_1274, 0);
lean_inc(x_1287);
lean_dec(x_1274);
x_1224 = x_1287;
x_1225 = x_1266;
goto block_1262;
}
}
else
{
uint8_t x_1288; 
lean_dec(x_1222);
lean_dec(x_1179);
lean_dec(x_1174);
lean_dec(x_1167);
lean_dec(x_2);
x_1288 = !lean_is_exclusive(x_1264);
if (x_1288 == 0)
{
return x_1264;
}
else
{
lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; 
x_1289 = lean_ctor_get(x_1264, 0);
x_1290 = lean_ctor_get(x_1264, 1);
lean_inc(x_1290);
lean_inc(x_1289);
lean_dec(x_1264);
x_1291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1291, 0, x_1289);
lean_ctor_set(x_1291, 1, x_1290);
return x_1291;
}
}
block_1262:
{
lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; uint8_t x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; 
x_1226 = lean_mk_syntax_ident(x_1167);
x_1227 = l_Lean_mkOptionalNode___closed__2;
x_1228 = lean_array_push(x_1227, x_1226);
x_1229 = l_Lean_nullKind;
x_1230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1230, 0, x_1229);
lean_ctor_set(x_1230, 1, x_1228);
x_1231 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
x_1232 = 1;
x_1233 = lean_box(0);
lean_inc(x_1179);
x_1234 = lean_add_attribute(x_1224, x_1179, x_1231, x_1230, x_1232, x_1233);
x_1235 = lean_box(0);
x_1236 = l_Lean_mkConst(x_1179, x_1235);
if (lean_obj_tag(x_1234) == 0)
{
lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; 
x_1249 = lean_ctor_get(x_1234, 0);
lean_inc(x_1249);
lean_dec(x_1234);
x_1250 = l_Lean_Meta_setEnv(x_1249, x_2, x_1225);
x_1251 = lean_ctor_get(x_1250, 1);
lean_inc(x_1251);
lean_dec(x_1250);
x_1237 = x_1251;
goto block_1248;
}
else
{
lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; uint8_t x_1258; 
lean_dec(x_1236);
lean_dec(x_1174);
x_1252 = lean_ctor_get(x_1234, 0);
lean_inc(x_1252);
lean_dec(x_1234);
x_1253 = lean_io_error_to_string(x_1252);
x_1254 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1254, 0, x_1253);
x_1255 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1255, 0, x_1254);
x_1256 = lean_box(0);
x_1257 = l_Lean_Meta_throwOther___rarg(x_1255, x_1256, x_2, x_1225);
lean_dec(x_2);
x_1258 = !lean_is_exclusive(x_1257);
if (x_1258 == 0)
{
return x_1257;
}
else
{
lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; 
x_1259 = lean_ctor_get(x_1257, 0);
x_1260 = lean_ctor_get(x_1257, 1);
lean_inc(x_1260);
lean_inc(x_1259);
lean_dec(x_1257);
x_1261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1261, 0, x_1259);
lean_ctor_set(x_1261, 1, x_1260);
return x_1261;
}
}
block_1248:
{
lean_object* x_1238; 
lean_inc(x_2);
lean_inc(x_1236);
x_1238 = l_Lean_Meta_inferType(x_1236, x_2, x_1237);
if (lean_obj_tag(x_1238) == 0)
{
lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; 
x_1239 = lean_ctor_get(x_1238, 0);
lean_inc(x_1239);
x_1240 = lean_ctor_get(x_1238, 1);
lean_inc(x_1240);
lean_dec(x_1238);
x_1241 = l_Lean_mkAppStx___closed__2;
x_1242 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__23___boxed), 8, 4);
lean_closure_set(x_1242, 0, x_1184);
lean_closure_set(x_1242, 1, x_1241);
lean_closure_set(x_1242, 2, x_1174);
lean_closure_set(x_1242, 3, x_1236);
x_1243 = l_Lean_Meta_forallTelescope___rarg(x_1239, x_1242, x_2, x_1240);
return x_1243;
}
else
{
uint8_t x_1244; 
lean_dec(x_1236);
lean_dec(x_1174);
lean_dec(x_2);
x_1244 = !lean_is_exclusive(x_1238);
if (x_1244 == 0)
{
return x_1238;
}
else
{
lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; 
x_1245 = lean_ctor_get(x_1238, 0);
x_1246 = lean_ctor_get(x_1238, 1);
lean_inc(x_1246);
lean_inc(x_1245);
lean_dec(x_1238);
x_1247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1247, 0, x_1245);
lean_ctor_set(x_1247, 1, x_1246);
return x_1247;
}
}
}
}
}
else
{
uint8_t x_1292; 
lean_dec(x_1183);
lean_dec(x_1179);
lean_dec(x_1174);
lean_dec(x_1167);
lean_dec(x_2);
x_1292 = !lean_is_exclusive(x_1221);
if (x_1292 == 0)
{
return x_1221;
}
else
{
lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; 
x_1293 = lean_ctor_get(x_1221, 0);
x_1294 = lean_ctor_get(x_1221, 1);
lean_inc(x_1294);
lean_inc(x_1293);
lean_dec(x_1221);
x_1295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1295, 0, x_1293);
lean_ctor_set(x_1295, 1, x_1294);
return x_1295;
}
}
}
}
}
else
{
uint8_t x_1296; 
lean_dec(x_1183);
lean_dec(x_1181);
lean_dec(x_1179);
lean_dec(x_1174);
lean_dec(x_1167);
lean_dec(x_5);
lean_dec(x_2);
x_1296 = !lean_is_exclusive(x_1185);
if (x_1296 == 0)
{
return x_1185;
}
else
{
lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; 
x_1297 = lean_ctor_get(x_1185, 0);
x_1298 = lean_ctor_get(x_1185, 1);
lean_inc(x_1298);
lean_inc(x_1297);
lean_dec(x_1185);
x_1299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1299, 0, x_1297);
lean_ctor_set(x_1299, 1, x_1298);
return x_1299;
}
}
}
else
{
uint8_t x_1300; 
lean_dec(x_1179);
lean_dec(x_1174);
lean_dec(x_1167);
lean_dec(x_5);
lean_dec(x_2);
x_1300 = !lean_is_exclusive(x_1180);
if (x_1300 == 0)
{
return x_1180;
}
else
{
lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; 
x_1301 = lean_ctor_get(x_1180, 0);
x_1302 = lean_ctor_get(x_1180, 1);
lean_inc(x_1302);
lean_inc(x_1301);
lean_dec(x_1180);
x_1303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1303, 0, x_1301);
lean_ctor_set(x_1303, 1, x_1302);
return x_1303;
}
}
}
else
{
lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; 
lean_dec(x_1167);
lean_dec(x_5);
x_1304 = lean_ctor_get(x_1177, 0);
lean_inc(x_1304);
lean_dec(x_1177);
x_1305 = lean_box(0);
x_1306 = l_Lean_mkConst(x_1304, x_1305);
lean_inc(x_2);
lean_inc(x_1306);
x_1307 = l_Lean_Meta_inferType(x_1306, x_2, x_1154);
if (lean_obj_tag(x_1307) == 0)
{
lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; 
x_1308 = lean_ctor_get(x_1307, 0);
lean_inc(x_1308);
x_1309 = lean_ctor_get(x_1307, 1);
lean_inc(x_1309);
lean_dec(x_1307);
x_1310 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__25___boxed), 6, 2);
lean_closure_set(x_1310, 0, x_1174);
lean_closure_set(x_1310, 1, x_1306);
x_1311 = l_Lean_Meta_forallTelescope___rarg(x_1308, x_1310, x_2, x_1309);
return x_1311;
}
else
{
uint8_t x_1312; 
lean_dec(x_1306);
lean_dec(x_1174);
lean_dec(x_2);
x_1312 = !lean_is_exclusive(x_1307);
if (x_1312 == 0)
{
return x_1307;
}
else
{
lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; 
x_1313 = lean_ctor_get(x_1307, 0);
x_1314 = lean_ctor_get(x_1307, 1);
lean_inc(x_1314);
lean_inc(x_1313);
lean_dec(x_1307);
x_1315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1315, 0, x_1313);
lean_ctor_set(x_1315, 1, x_1314);
return x_1315;
}
}
}
}
else
{
lean_object* x_1316; 
lean_dec(x_1155);
x_1316 = lean_box(0);
x_1156 = x_1316;
goto block_1166;
}
block_1166:
{
lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; 
lean_dec(x_1156);
x_1157 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1158 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1158, 0, x_1157);
x_1159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1159, 0, x_1158);
x_1160 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_1161 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1161, 0, x_1160);
lean_ctor_set(x_1161, 1, x_1159);
x_1162 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_1163 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1163, 0, x_1161);
lean_ctor_set(x_1163, 1, x_1162);
x_1164 = lean_box(0);
x_1165 = l_Lean_Meta_throwOther___rarg(x_1163, x_1164, x_2, x_1154);
lean_dec(x_2);
return x_1165;
}
}
case 10:
{
lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; 
x_1317 = lean_ctor_get(x_4, 1);
lean_inc(x_1317);
lean_dec(x_4);
x_1318 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_1318) == 4)
{
lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; 
x_1330 = lean_ctor_get(x_1318, 0);
lean_inc(x_1330);
lean_dec(x_1318);
x_1331 = lean_unsigned_to_nat(0u);
x_1332 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_1331);
x_1333 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1332);
x_1334 = lean_mk_array(x_1332, x_1333);
x_1335 = lean_unsigned_to_nat(1u);
x_1336 = lean_nat_sub(x_1332, x_1335);
lean_dec(x_1332);
lean_inc(x_5);
x_1337 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_1334, x_1336);
x_1338 = lean_ctor_get(x_1317, 0);
lean_inc(x_1338);
x_1339 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_1340 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_1339, x_1338, x_1330);
lean_dec(x_1338);
if (lean_obj_tag(x_1340) == 0)
{
lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; 
x_1341 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_1342 = l_Lean_Name_append___main(x_1330, x_1341);
lean_inc(x_1330);
x_1343 = l_Lean_Meta_getConstInfo(x_1330, x_2, x_1317);
if (lean_obj_tag(x_1343) == 0)
{
lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; 
x_1344 = lean_ctor_get(x_1343, 0);
lean_inc(x_1344);
x_1345 = lean_ctor_get(x_1343, 1);
lean_inc(x_1345);
lean_dec(x_1343);
x_1346 = l_Lean_ConstantInfo_type(x_1344);
x_1347 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_1346);
x_1348 = l_Lean_Meta_forallTelescope___rarg(x_1346, x_1347, x_2, x_1345);
if (lean_obj_tag(x_1348) == 0)
{
lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; uint8_t x_1352; 
x_1349 = lean_ctor_get(x_1348, 0);
lean_inc(x_1349);
x_1350 = lean_ctor_get(x_1348, 1);
lean_inc(x_1350);
lean_dec(x_1348);
x_1351 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_1352 = l_Lean_Expr_isConstOf(x_1349, x_1351);
lean_dec(x_1349);
if (x_1352 == 0)
{
lean_object* x_1353; 
lean_dec(x_1346);
lean_dec(x_1344);
lean_dec(x_1342);
lean_dec(x_1337);
lean_dec(x_1330);
lean_inc(x_2);
lean_inc(x_5);
x_1353 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_1350);
if (lean_obj_tag(x_1353) == 0)
{
lean_object* x_1354; 
x_1354 = lean_ctor_get(x_1353, 0);
lean_inc(x_1354);
if (lean_obj_tag(x_1354) == 0)
{
lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; 
x_1355 = lean_ctor_get(x_1353, 1);
lean_inc(x_1355);
lean_dec(x_1353);
x_1356 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1357 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1357, 0, x_1356);
x_1358 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1358, 0, x_1357);
x_1359 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_1360 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1360, 0, x_1359);
lean_ctor_set(x_1360, 1, x_1358);
x_1361 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_1362 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1362, 0, x_1360);
lean_ctor_set(x_1362, 1, x_1361);
x_1363 = lean_box(0);
x_1364 = l_Lean_Meta_throwOther___rarg(x_1362, x_1363, x_2, x_1355);
lean_dec(x_2);
return x_1364;
}
else
{
lean_object* x_1365; lean_object* x_1366; 
lean_dec(x_5);
x_1365 = lean_ctor_get(x_1353, 1);
lean_inc(x_1365);
lean_dec(x_1353);
x_1366 = lean_ctor_get(x_1354, 0);
lean_inc(x_1366);
lean_dec(x_1354);
x_1 = x_1366;
x_3 = x_1365;
goto _start;
}
}
else
{
uint8_t x_1368; 
lean_dec(x_5);
lean_dec(x_2);
x_1368 = !lean_is_exclusive(x_1353);
if (x_1368 == 0)
{
return x_1353;
}
else
{
lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; 
x_1369 = lean_ctor_get(x_1353, 0);
x_1370 = lean_ctor_get(x_1353, 1);
lean_inc(x_1370);
lean_inc(x_1369);
lean_dec(x_1353);
x_1371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1371, 0, x_1369);
lean_ctor_set(x_1371, 1, x_1370);
return x_1371;
}
}
}
else
{
lean_object* x_1372; 
x_1372 = l_Lean_ConstantInfo_value_x3f(x_1344);
lean_dec(x_1344);
if (lean_obj_tag(x_1372) == 0)
{
lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; 
lean_dec(x_1346);
lean_dec(x_1342);
lean_dec(x_1337);
lean_dec(x_1330);
x_1373 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1374 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1374, 0, x_1373);
x_1375 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1375, 0, x_1374);
x_1376 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__9;
x_1377 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1377, 0, x_1376);
lean_ctor_set(x_1377, 1, x_1375);
x_1378 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_1379 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1379, 0, x_1377);
lean_ctor_set(x_1379, 1, x_1378);
x_1380 = lean_box(0);
x_1381 = l_Lean_Meta_throwOther___rarg(x_1379, x_1380, x_2, x_1350);
lean_dec(x_2);
return x_1381;
}
else
{
lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; 
lean_dec(x_5);
x_1382 = lean_ctor_get(x_1372, 0);
lean_inc(x_1382);
lean_dec(x_1372);
x_1383 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_1382);
lean_inc(x_2);
x_1384 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_1383, x_2, x_1350);
if (lean_obj_tag(x_1384) == 0)
{
lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1426; lean_object* x_1427; 
x_1385 = lean_ctor_get(x_1384, 0);
lean_inc(x_1385);
x_1386 = lean_ctor_get(x_1384, 1);
lean_inc(x_1386);
lean_dec(x_1384);
x_1426 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__19;
lean_inc(x_2);
x_1427 = l_Lean_Meta_forallTelescope___rarg(x_1346, x_1426, x_2, x_1386);
if (lean_obj_tag(x_1427) == 0)
{
lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; uint8_t x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; 
x_1428 = lean_ctor_get(x_1427, 0);
lean_inc(x_1428);
x_1429 = lean_ctor_get(x_1427, 1);
lean_inc(x_1429);
lean_dec(x_1427);
lean_inc(x_1342);
x_1430 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1430, 0, x_1342);
lean_ctor_set(x_1430, 1, x_1340);
lean_ctor_set(x_1430, 2, x_1428);
x_1431 = lean_box(0);
x_1432 = 0;
x_1433 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1433, 0, x_1430);
lean_ctor_set(x_1433, 1, x_1385);
lean_ctor_set(x_1433, 2, x_1431);
lean_ctor_set_uint8(x_1433, sizeof(void*)*3, x_1432);
x_1434 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1434, 0, x_1433);
x_1435 = lean_ctor_get(x_1429, 0);
lean_inc(x_1435);
x_1436 = l_Lean_Options_empty;
x_1437 = l_Lean_Environment_addAndCompile(x_1435, x_1436, x_1434);
lean_dec(x_1434);
if (lean_obj_tag(x_1437) == 0)
{
lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; uint8_t x_1446; 
lean_dec(x_1342);
lean_dec(x_1337);
lean_dec(x_1330);
x_1438 = lean_ctor_get(x_1437, 0);
lean_inc(x_1438);
lean_dec(x_1437);
x_1439 = l_Lean_KernelException_toMessageData(x_1438, x_1436);
x_1440 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1439);
x_1441 = l_Lean_Format_pretty(x_1440, x_1436);
x_1442 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1442, 0, x_1441);
x_1443 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1443, 0, x_1442);
x_1444 = lean_box(0);
x_1445 = l_Lean_Meta_throwOther___rarg(x_1443, x_1444, x_2, x_1429);
lean_dec(x_2);
x_1446 = !lean_is_exclusive(x_1445);
if (x_1446 == 0)
{
return x_1445;
}
else
{
lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; 
x_1447 = lean_ctor_get(x_1445, 0);
x_1448 = lean_ctor_get(x_1445, 1);
lean_inc(x_1448);
lean_inc(x_1447);
lean_dec(x_1445);
x_1449 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1449, 0, x_1447);
lean_ctor_set(x_1449, 1, x_1448);
return x_1449;
}
}
else
{
lean_object* x_1450; 
x_1450 = lean_ctor_get(x_1437, 0);
lean_inc(x_1450);
lean_dec(x_1437);
x_1387 = x_1450;
x_1388 = x_1429;
goto block_1425;
}
}
else
{
uint8_t x_1451; 
lean_dec(x_1385);
lean_dec(x_1342);
lean_dec(x_1337);
lean_dec(x_1330);
lean_dec(x_2);
x_1451 = !lean_is_exclusive(x_1427);
if (x_1451 == 0)
{
return x_1427;
}
else
{
lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; 
x_1452 = lean_ctor_get(x_1427, 0);
x_1453 = lean_ctor_get(x_1427, 1);
lean_inc(x_1453);
lean_inc(x_1452);
lean_dec(x_1427);
x_1454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1454, 0, x_1452);
lean_ctor_set(x_1454, 1, x_1453);
return x_1454;
}
}
block_1425:
{
lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; uint8_t x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; 
x_1389 = lean_mk_syntax_ident(x_1330);
x_1390 = l_Lean_mkOptionalNode___closed__2;
x_1391 = lean_array_push(x_1390, x_1389);
x_1392 = l_Lean_nullKind;
x_1393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1393, 0, x_1392);
lean_ctor_set(x_1393, 1, x_1391);
x_1394 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
x_1395 = 1;
x_1396 = lean_box(0);
lean_inc(x_1342);
x_1397 = lean_add_attribute(x_1387, x_1342, x_1394, x_1393, x_1395, x_1396);
x_1398 = lean_box(0);
x_1399 = l_Lean_mkConst(x_1342, x_1398);
if (lean_obj_tag(x_1397) == 0)
{
lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; 
x_1412 = lean_ctor_get(x_1397, 0);
lean_inc(x_1412);
lean_dec(x_1397);
x_1413 = l_Lean_Meta_setEnv(x_1412, x_2, x_1388);
x_1414 = lean_ctor_get(x_1413, 1);
lean_inc(x_1414);
lean_dec(x_1413);
x_1400 = x_1414;
goto block_1411;
}
else
{
lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; uint8_t x_1421; 
lean_dec(x_1399);
lean_dec(x_1337);
x_1415 = lean_ctor_get(x_1397, 0);
lean_inc(x_1415);
lean_dec(x_1397);
x_1416 = lean_io_error_to_string(x_1415);
x_1417 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1417, 0, x_1416);
x_1418 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1418, 0, x_1417);
x_1419 = lean_box(0);
x_1420 = l_Lean_Meta_throwOther___rarg(x_1418, x_1419, x_2, x_1388);
lean_dec(x_2);
x_1421 = !lean_is_exclusive(x_1420);
if (x_1421 == 0)
{
return x_1420;
}
else
{
lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; 
x_1422 = lean_ctor_get(x_1420, 0);
x_1423 = lean_ctor_get(x_1420, 1);
lean_inc(x_1423);
lean_inc(x_1422);
lean_dec(x_1420);
x_1424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1424, 0, x_1422);
lean_ctor_set(x_1424, 1, x_1423);
return x_1424;
}
}
block_1411:
{
lean_object* x_1401; 
lean_inc(x_2);
lean_inc(x_1399);
x_1401 = l_Lean_Meta_inferType(x_1399, x_2, x_1400);
if (lean_obj_tag(x_1401) == 0)
{
lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; 
x_1402 = lean_ctor_get(x_1401, 0);
lean_inc(x_1402);
x_1403 = lean_ctor_get(x_1401, 1);
lean_inc(x_1403);
lean_dec(x_1401);
x_1404 = l_Lean_mkAppStx___closed__2;
x_1405 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__26___boxed), 8, 4);
lean_closure_set(x_1405, 0, x_1347);
lean_closure_set(x_1405, 1, x_1404);
lean_closure_set(x_1405, 2, x_1337);
lean_closure_set(x_1405, 3, x_1399);
x_1406 = l_Lean_Meta_forallTelescope___rarg(x_1402, x_1405, x_2, x_1403);
return x_1406;
}
else
{
uint8_t x_1407; 
lean_dec(x_1399);
lean_dec(x_1337);
lean_dec(x_2);
x_1407 = !lean_is_exclusive(x_1401);
if (x_1407 == 0)
{
return x_1401;
}
else
{
lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; 
x_1408 = lean_ctor_get(x_1401, 0);
x_1409 = lean_ctor_get(x_1401, 1);
lean_inc(x_1409);
lean_inc(x_1408);
lean_dec(x_1401);
x_1410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1410, 0, x_1408);
lean_ctor_set(x_1410, 1, x_1409);
return x_1410;
}
}
}
}
}
else
{
uint8_t x_1455; 
lean_dec(x_1346);
lean_dec(x_1342);
lean_dec(x_1337);
lean_dec(x_1330);
lean_dec(x_2);
x_1455 = !lean_is_exclusive(x_1384);
if (x_1455 == 0)
{
return x_1384;
}
else
{
lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; 
x_1456 = lean_ctor_get(x_1384, 0);
x_1457 = lean_ctor_get(x_1384, 1);
lean_inc(x_1457);
lean_inc(x_1456);
lean_dec(x_1384);
x_1458 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1458, 0, x_1456);
lean_ctor_set(x_1458, 1, x_1457);
return x_1458;
}
}
}
}
}
else
{
uint8_t x_1459; 
lean_dec(x_1346);
lean_dec(x_1344);
lean_dec(x_1342);
lean_dec(x_1337);
lean_dec(x_1330);
lean_dec(x_5);
lean_dec(x_2);
x_1459 = !lean_is_exclusive(x_1348);
if (x_1459 == 0)
{
return x_1348;
}
else
{
lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; 
x_1460 = lean_ctor_get(x_1348, 0);
x_1461 = lean_ctor_get(x_1348, 1);
lean_inc(x_1461);
lean_inc(x_1460);
lean_dec(x_1348);
x_1462 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1462, 0, x_1460);
lean_ctor_set(x_1462, 1, x_1461);
return x_1462;
}
}
}
else
{
uint8_t x_1463; 
lean_dec(x_1342);
lean_dec(x_1337);
lean_dec(x_1330);
lean_dec(x_5);
lean_dec(x_2);
x_1463 = !lean_is_exclusive(x_1343);
if (x_1463 == 0)
{
return x_1343;
}
else
{
lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; 
x_1464 = lean_ctor_get(x_1343, 0);
x_1465 = lean_ctor_get(x_1343, 1);
lean_inc(x_1465);
lean_inc(x_1464);
lean_dec(x_1343);
x_1466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1466, 0, x_1464);
lean_ctor_set(x_1466, 1, x_1465);
return x_1466;
}
}
}
else
{
lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; 
lean_dec(x_1330);
lean_dec(x_5);
x_1467 = lean_ctor_get(x_1340, 0);
lean_inc(x_1467);
lean_dec(x_1340);
x_1468 = lean_box(0);
x_1469 = l_Lean_mkConst(x_1467, x_1468);
lean_inc(x_2);
lean_inc(x_1469);
x_1470 = l_Lean_Meta_inferType(x_1469, x_2, x_1317);
if (lean_obj_tag(x_1470) == 0)
{
lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; 
x_1471 = lean_ctor_get(x_1470, 0);
lean_inc(x_1471);
x_1472 = lean_ctor_get(x_1470, 1);
lean_inc(x_1472);
lean_dec(x_1470);
x_1473 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__28___boxed), 6, 2);
lean_closure_set(x_1473, 0, x_1337);
lean_closure_set(x_1473, 1, x_1469);
x_1474 = l_Lean_Meta_forallTelescope___rarg(x_1471, x_1473, x_2, x_1472);
return x_1474;
}
else
{
uint8_t x_1475; 
lean_dec(x_1469);
lean_dec(x_1337);
lean_dec(x_2);
x_1475 = !lean_is_exclusive(x_1470);
if (x_1475 == 0)
{
return x_1470;
}
else
{
lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; 
x_1476 = lean_ctor_get(x_1470, 0);
x_1477 = lean_ctor_get(x_1470, 1);
lean_inc(x_1477);
lean_inc(x_1476);
lean_dec(x_1470);
x_1478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1478, 0, x_1476);
lean_ctor_set(x_1478, 1, x_1477);
return x_1478;
}
}
}
}
else
{
lean_object* x_1479; 
lean_dec(x_1318);
x_1479 = lean_box(0);
x_1319 = x_1479;
goto block_1329;
}
block_1329:
{
lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; 
lean_dec(x_1319);
x_1320 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1321 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1321, 0, x_1320);
x_1322 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1322, 0, x_1321);
x_1323 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_1324 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1324, 0, x_1323);
lean_ctor_set(x_1324, 1, x_1322);
x_1325 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_1326 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1326, 0, x_1324);
lean_ctor_set(x_1326, 1, x_1325);
x_1327 = lean_box(0);
x_1328 = l_Lean_Meta_throwOther___rarg(x_1326, x_1327, x_2, x_1317);
lean_dec(x_2);
return x_1328;
}
}
case 11:
{
lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; 
x_1480 = lean_ctor_get(x_4, 1);
lean_inc(x_1480);
lean_dec(x_4);
x_1481 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_1481) == 4)
{
lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; 
x_1493 = lean_ctor_get(x_1481, 0);
lean_inc(x_1493);
lean_dec(x_1481);
x_1494 = lean_unsigned_to_nat(0u);
x_1495 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_1494);
x_1496 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1495);
x_1497 = lean_mk_array(x_1495, x_1496);
x_1498 = lean_unsigned_to_nat(1u);
x_1499 = lean_nat_sub(x_1495, x_1498);
lean_dec(x_1495);
lean_inc(x_5);
x_1500 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_1497, x_1499);
x_1501 = lean_ctor_get(x_1480, 0);
lean_inc(x_1501);
x_1502 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_1503 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_1502, x_1501, x_1493);
lean_dec(x_1501);
if (lean_obj_tag(x_1503) == 0)
{
lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; 
x_1504 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_1505 = l_Lean_Name_append___main(x_1493, x_1504);
lean_inc(x_1493);
x_1506 = l_Lean_Meta_getConstInfo(x_1493, x_2, x_1480);
if (lean_obj_tag(x_1506) == 0)
{
lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; 
x_1507 = lean_ctor_get(x_1506, 0);
lean_inc(x_1507);
x_1508 = lean_ctor_get(x_1506, 1);
lean_inc(x_1508);
lean_dec(x_1506);
x_1509 = l_Lean_ConstantInfo_type(x_1507);
x_1510 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_1509);
x_1511 = l_Lean_Meta_forallTelescope___rarg(x_1509, x_1510, x_2, x_1508);
if (lean_obj_tag(x_1511) == 0)
{
lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; uint8_t x_1515; 
x_1512 = lean_ctor_get(x_1511, 0);
lean_inc(x_1512);
x_1513 = lean_ctor_get(x_1511, 1);
lean_inc(x_1513);
lean_dec(x_1511);
x_1514 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_1515 = l_Lean_Expr_isConstOf(x_1512, x_1514);
lean_dec(x_1512);
if (x_1515 == 0)
{
lean_object* x_1516; 
lean_dec(x_1509);
lean_dec(x_1507);
lean_dec(x_1505);
lean_dec(x_1500);
lean_dec(x_1493);
lean_inc(x_2);
lean_inc(x_5);
x_1516 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_1513);
if (lean_obj_tag(x_1516) == 0)
{
lean_object* x_1517; 
x_1517 = lean_ctor_get(x_1516, 0);
lean_inc(x_1517);
if (lean_obj_tag(x_1517) == 0)
{
lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; 
x_1518 = lean_ctor_get(x_1516, 1);
lean_inc(x_1518);
lean_dec(x_1516);
x_1519 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1520 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1520, 0, x_1519);
x_1521 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1521, 0, x_1520);
x_1522 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_1523 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1523, 0, x_1522);
lean_ctor_set(x_1523, 1, x_1521);
x_1524 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_1525 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1525, 0, x_1523);
lean_ctor_set(x_1525, 1, x_1524);
x_1526 = lean_box(0);
x_1527 = l_Lean_Meta_throwOther___rarg(x_1525, x_1526, x_2, x_1518);
lean_dec(x_2);
return x_1527;
}
else
{
lean_object* x_1528; lean_object* x_1529; 
lean_dec(x_5);
x_1528 = lean_ctor_get(x_1516, 1);
lean_inc(x_1528);
lean_dec(x_1516);
x_1529 = lean_ctor_get(x_1517, 0);
lean_inc(x_1529);
lean_dec(x_1517);
x_1 = x_1529;
x_3 = x_1528;
goto _start;
}
}
else
{
uint8_t x_1531; 
lean_dec(x_5);
lean_dec(x_2);
x_1531 = !lean_is_exclusive(x_1516);
if (x_1531 == 0)
{
return x_1516;
}
else
{
lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; 
x_1532 = lean_ctor_get(x_1516, 0);
x_1533 = lean_ctor_get(x_1516, 1);
lean_inc(x_1533);
lean_inc(x_1532);
lean_dec(x_1516);
x_1534 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1534, 0, x_1532);
lean_ctor_set(x_1534, 1, x_1533);
return x_1534;
}
}
}
else
{
lean_object* x_1535; 
x_1535 = l_Lean_ConstantInfo_value_x3f(x_1507);
lean_dec(x_1507);
if (lean_obj_tag(x_1535) == 0)
{
lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; 
lean_dec(x_1509);
lean_dec(x_1505);
lean_dec(x_1500);
lean_dec(x_1493);
x_1536 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1537 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1537, 0, x_1536);
x_1538 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1538, 0, x_1537);
x_1539 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__9;
x_1540 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1540, 0, x_1539);
lean_ctor_set(x_1540, 1, x_1538);
x_1541 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_1542 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1542, 0, x_1540);
lean_ctor_set(x_1542, 1, x_1541);
x_1543 = lean_box(0);
x_1544 = l_Lean_Meta_throwOther___rarg(x_1542, x_1543, x_2, x_1513);
lean_dec(x_2);
return x_1544;
}
else
{
lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; 
lean_dec(x_5);
x_1545 = lean_ctor_get(x_1535, 0);
lean_inc(x_1545);
lean_dec(x_1535);
x_1546 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_1545);
lean_inc(x_2);
x_1547 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_1546, x_2, x_1513);
if (lean_obj_tag(x_1547) == 0)
{
lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1589; lean_object* x_1590; 
x_1548 = lean_ctor_get(x_1547, 0);
lean_inc(x_1548);
x_1549 = lean_ctor_get(x_1547, 1);
lean_inc(x_1549);
lean_dec(x_1547);
x_1589 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__20;
lean_inc(x_2);
x_1590 = l_Lean_Meta_forallTelescope___rarg(x_1509, x_1589, x_2, x_1549);
if (lean_obj_tag(x_1590) == 0)
{
lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; uint8_t x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; 
x_1591 = lean_ctor_get(x_1590, 0);
lean_inc(x_1591);
x_1592 = lean_ctor_get(x_1590, 1);
lean_inc(x_1592);
lean_dec(x_1590);
lean_inc(x_1505);
x_1593 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1593, 0, x_1505);
lean_ctor_set(x_1593, 1, x_1503);
lean_ctor_set(x_1593, 2, x_1591);
x_1594 = lean_box(0);
x_1595 = 0;
x_1596 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1596, 0, x_1593);
lean_ctor_set(x_1596, 1, x_1548);
lean_ctor_set(x_1596, 2, x_1594);
lean_ctor_set_uint8(x_1596, sizeof(void*)*3, x_1595);
x_1597 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1597, 0, x_1596);
x_1598 = lean_ctor_get(x_1592, 0);
lean_inc(x_1598);
x_1599 = l_Lean_Options_empty;
x_1600 = l_Lean_Environment_addAndCompile(x_1598, x_1599, x_1597);
lean_dec(x_1597);
if (lean_obj_tag(x_1600) == 0)
{
lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; uint8_t x_1609; 
lean_dec(x_1505);
lean_dec(x_1500);
lean_dec(x_1493);
x_1601 = lean_ctor_get(x_1600, 0);
lean_inc(x_1601);
lean_dec(x_1600);
x_1602 = l_Lean_KernelException_toMessageData(x_1601, x_1599);
x_1603 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1602);
x_1604 = l_Lean_Format_pretty(x_1603, x_1599);
x_1605 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1605, 0, x_1604);
x_1606 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1606, 0, x_1605);
x_1607 = lean_box(0);
x_1608 = l_Lean_Meta_throwOther___rarg(x_1606, x_1607, x_2, x_1592);
lean_dec(x_2);
x_1609 = !lean_is_exclusive(x_1608);
if (x_1609 == 0)
{
return x_1608;
}
else
{
lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; 
x_1610 = lean_ctor_get(x_1608, 0);
x_1611 = lean_ctor_get(x_1608, 1);
lean_inc(x_1611);
lean_inc(x_1610);
lean_dec(x_1608);
x_1612 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1612, 0, x_1610);
lean_ctor_set(x_1612, 1, x_1611);
return x_1612;
}
}
else
{
lean_object* x_1613; 
x_1613 = lean_ctor_get(x_1600, 0);
lean_inc(x_1613);
lean_dec(x_1600);
x_1550 = x_1613;
x_1551 = x_1592;
goto block_1588;
}
}
else
{
uint8_t x_1614; 
lean_dec(x_1548);
lean_dec(x_1505);
lean_dec(x_1500);
lean_dec(x_1493);
lean_dec(x_2);
x_1614 = !lean_is_exclusive(x_1590);
if (x_1614 == 0)
{
return x_1590;
}
else
{
lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; 
x_1615 = lean_ctor_get(x_1590, 0);
x_1616 = lean_ctor_get(x_1590, 1);
lean_inc(x_1616);
lean_inc(x_1615);
lean_dec(x_1590);
x_1617 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1617, 0, x_1615);
lean_ctor_set(x_1617, 1, x_1616);
return x_1617;
}
}
block_1588:
{
lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; uint8_t x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; 
x_1552 = lean_mk_syntax_ident(x_1493);
x_1553 = l_Lean_mkOptionalNode___closed__2;
x_1554 = lean_array_push(x_1553, x_1552);
x_1555 = l_Lean_nullKind;
x_1556 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1556, 0, x_1555);
lean_ctor_set(x_1556, 1, x_1554);
x_1557 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
x_1558 = 1;
x_1559 = lean_box(0);
lean_inc(x_1505);
x_1560 = lean_add_attribute(x_1550, x_1505, x_1557, x_1556, x_1558, x_1559);
x_1561 = lean_box(0);
x_1562 = l_Lean_mkConst(x_1505, x_1561);
if (lean_obj_tag(x_1560) == 0)
{
lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; 
x_1575 = lean_ctor_get(x_1560, 0);
lean_inc(x_1575);
lean_dec(x_1560);
x_1576 = l_Lean_Meta_setEnv(x_1575, x_2, x_1551);
x_1577 = lean_ctor_get(x_1576, 1);
lean_inc(x_1577);
lean_dec(x_1576);
x_1563 = x_1577;
goto block_1574;
}
else
{
lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; uint8_t x_1584; 
lean_dec(x_1562);
lean_dec(x_1500);
x_1578 = lean_ctor_get(x_1560, 0);
lean_inc(x_1578);
lean_dec(x_1560);
x_1579 = lean_io_error_to_string(x_1578);
x_1580 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1580, 0, x_1579);
x_1581 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1581, 0, x_1580);
x_1582 = lean_box(0);
x_1583 = l_Lean_Meta_throwOther___rarg(x_1581, x_1582, x_2, x_1551);
lean_dec(x_2);
x_1584 = !lean_is_exclusive(x_1583);
if (x_1584 == 0)
{
return x_1583;
}
else
{
lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; 
x_1585 = lean_ctor_get(x_1583, 0);
x_1586 = lean_ctor_get(x_1583, 1);
lean_inc(x_1586);
lean_inc(x_1585);
lean_dec(x_1583);
x_1587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1587, 0, x_1585);
lean_ctor_set(x_1587, 1, x_1586);
return x_1587;
}
}
block_1574:
{
lean_object* x_1564; 
lean_inc(x_2);
lean_inc(x_1562);
x_1564 = l_Lean_Meta_inferType(x_1562, x_2, x_1563);
if (lean_obj_tag(x_1564) == 0)
{
lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; 
x_1565 = lean_ctor_get(x_1564, 0);
lean_inc(x_1565);
x_1566 = lean_ctor_get(x_1564, 1);
lean_inc(x_1566);
lean_dec(x_1564);
x_1567 = l_Lean_mkAppStx___closed__2;
x_1568 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__29___boxed), 8, 4);
lean_closure_set(x_1568, 0, x_1510);
lean_closure_set(x_1568, 1, x_1567);
lean_closure_set(x_1568, 2, x_1500);
lean_closure_set(x_1568, 3, x_1562);
x_1569 = l_Lean_Meta_forallTelescope___rarg(x_1565, x_1568, x_2, x_1566);
return x_1569;
}
else
{
uint8_t x_1570; 
lean_dec(x_1562);
lean_dec(x_1500);
lean_dec(x_2);
x_1570 = !lean_is_exclusive(x_1564);
if (x_1570 == 0)
{
return x_1564;
}
else
{
lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; 
x_1571 = lean_ctor_get(x_1564, 0);
x_1572 = lean_ctor_get(x_1564, 1);
lean_inc(x_1572);
lean_inc(x_1571);
lean_dec(x_1564);
x_1573 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1573, 0, x_1571);
lean_ctor_set(x_1573, 1, x_1572);
return x_1573;
}
}
}
}
}
else
{
uint8_t x_1618; 
lean_dec(x_1509);
lean_dec(x_1505);
lean_dec(x_1500);
lean_dec(x_1493);
lean_dec(x_2);
x_1618 = !lean_is_exclusive(x_1547);
if (x_1618 == 0)
{
return x_1547;
}
else
{
lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; 
x_1619 = lean_ctor_get(x_1547, 0);
x_1620 = lean_ctor_get(x_1547, 1);
lean_inc(x_1620);
lean_inc(x_1619);
lean_dec(x_1547);
x_1621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1621, 0, x_1619);
lean_ctor_set(x_1621, 1, x_1620);
return x_1621;
}
}
}
}
}
else
{
uint8_t x_1622; 
lean_dec(x_1509);
lean_dec(x_1507);
lean_dec(x_1505);
lean_dec(x_1500);
lean_dec(x_1493);
lean_dec(x_5);
lean_dec(x_2);
x_1622 = !lean_is_exclusive(x_1511);
if (x_1622 == 0)
{
return x_1511;
}
else
{
lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; 
x_1623 = lean_ctor_get(x_1511, 0);
x_1624 = lean_ctor_get(x_1511, 1);
lean_inc(x_1624);
lean_inc(x_1623);
lean_dec(x_1511);
x_1625 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1625, 0, x_1623);
lean_ctor_set(x_1625, 1, x_1624);
return x_1625;
}
}
}
else
{
uint8_t x_1626; 
lean_dec(x_1505);
lean_dec(x_1500);
lean_dec(x_1493);
lean_dec(x_5);
lean_dec(x_2);
x_1626 = !lean_is_exclusive(x_1506);
if (x_1626 == 0)
{
return x_1506;
}
else
{
lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; 
x_1627 = lean_ctor_get(x_1506, 0);
x_1628 = lean_ctor_get(x_1506, 1);
lean_inc(x_1628);
lean_inc(x_1627);
lean_dec(x_1506);
x_1629 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1629, 0, x_1627);
lean_ctor_set(x_1629, 1, x_1628);
return x_1629;
}
}
}
else
{
lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; 
lean_dec(x_1493);
lean_dec(x_5);
x_1630 = lean_ctor_get(x_1503, 0);
lean_inc(x_1630);
lean_dec(x_1503);
x_1631 = lean_box(0);
x_1632 = l_Lean_mkConst(x_1630, x_1631);
lean_inc(x_2);
lean_inc(x_1632);
x_1633 = l_Lean_Meta_inferType(x_1632, x_2, x_1480);
if (lean_obj_tag(x_1633) == 0)
{
lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; 
x_1634 = lean_ctor_get(x_1633, 0);
lean_inc(x_1634);
x_1635 = lean_ctor_get(x_1633, 1);
lean_inc(x_1635);
lean_dec(x_1633);
x_1636 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__31___boxed), 6, 2);
lean_closure_set(x_1636, 0, x_1500);
lean_closure_set(x_1636, 1, x_1632);
x_1637 = l_Lean_Meta_forallTelescope___rarg(x_1634, x_1636, x_2, x_1635);
return x_1637;
}
else
{
uint8_t x_1638; 
lean_dec(x_1632);
lean_dec(x_1500);
lean_dec(x_2);
x_1638 = !lean_is_exclusive(x_1633);
if (x_1638 == 0)
{
return x_1633;
}
else
{
lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; 
x_1639 = lean_ctor_get(x_1633, 0);
x_1640 = lean_ctor_get(x_1633, 1);
lean_inc(x_1640);
lean_inc(x_1639);
lean_dec(x_1633);
x_1641 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1641, 0, x_1639);
lean_ctor_set(x_1641, 1, x_1640);
return x_1641;
}
}
}
}
else
{
lean_object* x_1642; 
lean_dec(x_1481);
x_1642 = lean_box(0);
x_1482 = x_1642;
goto block_1492;
}
block_1492:
{
lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; 
lean_dec(x_1482);
x_1483 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1484 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1484, 0, x_1483);
x_1485 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1485, 0, x_1484);
x_1486 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_1487 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1487, 0, x_1486);
lean_ctor_set(x_1487, 1, x_1485);
x_1488 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_1489 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1489, 0, x_1487);
lean_ctor_set(x_1489, 1, x_1488);
x_1490 = lean_box(0);
x_1491 = l_Lean_Meta_throwOther___rarg(x_1489, x_1490, x_2, x_1480);
lean_dec(x_2);
return x_1491;
}
}
default: 
{
lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; 
x_1643 = lean_ctor_get(x_4, 1);
lean_inc(x_1643);
lean_dec(x_4);
x_1644 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_1644) == 4)
{
lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; 
x_1656 = lean_ctor_get(x_1644, 0);
lean_inc(x_1656);
lean_dec(x_1644);
x_1657 = lean_unsigned_to_nat(0u);
x_1658 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_1657);
x_1659 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_1658);
x_1660 = lean_mk_array(x_1658, x_1659);
x_1661 = lean_unsigned_to_nat(1u);
x_1662 = lean_nat_sub(x_1658, x_1661);
lean_dec(x_1658);
lean_inc(x_5);
x_1663 = l___private_Lean_Expr_3__getAppArgsAux___main(x_5, x_1660, x_1662);
x_1664 = lean_ctor_get(x_1643, 0);
lean_inc(x_1664);
x_1665 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
x_1666 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_1665, x_1664, x_1656);
lean_dec(x_1664);
if (lean_obj_tag(x_1666) == 0)
{
lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; 
x_1667 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_1668 = l_Lean_Name_append___main(x_1656, x_1667);
lean_inc(x_1656);
x_1669 = l_Lean_Meta_getConstInfo(x_1656, x_2, x_1643);
if (lean_obj_tag(x_1669) == 0)
{
lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; 
x_1670 = lean_ctor_get(x_1669, 0);
lean_inc(x_1670);
x_1671 = lean_ctor_get(x_1669, 1);
lean_inc(x_1671);
lean_dec(x_1669);
x_1672 = l_Lean_ConstantInfo_type(x_1670);
x_1673 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_inc(x_2);
lean_inc(x_1672);
x_1674 = l_Lean_Meta_forallTelescope___rarg(x_1672, x_1673, x_2, x_1671);
if (lean_obj_tag(x_1674) == 0)
{
lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; uint8_t x_1678; 
x_1675 = lean_ctor_get(x_1674, 0);
lean_inc(x_1675);
x_1676 = lean_ctor_get(x_1674, 1);
lean_inc(x_1676);
lean_dec(x_1674);
x_1677 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody___spec__1___closed__1;
x_1678 = l_Lean_Expr_isConstOf(x_1675, x_1677);
lean_dec(x_1675);
if (x_1678 == 0)
{
lean_object* x_1679; 
lean_dec(x_1672);
lean_dec(x_1670);
lean_dec(x_1668);
lean_dec(x_1663);
lean_dec(x_1656);
lean_inc(x_2);
lean_inc(x_5);
x_1679 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_5, x_2, x_1676);
if (lean_obj_tag(x_1679) == 0)
{
lean_object* x_1680; 
x_1680 = lean_ctor_get(x_1679, 0);
lean_inc(x_1680);
if (lean_obj_tag(x_1680) == 0)
{
lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; 
x_1681 = lean_ctor_get(x_1679, 1);
lean_inc(x_1681);
lean_dec(x_1679);
x_1682 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1683 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1683, 0, x_1682);
x_1684 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1684, 0, x_1683);
x_1685 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__6;
x_1686 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1686, 0, x_1685);
lean_ctor_set(x_1686, 1, x_1684);
x_1687 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_1688 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1688, 0, x_1686);
lean_ctor_set(x_1688, 1, x_1687);
x_1689 = lean_box(0);
x_1690 = l_Lean_Meta_throwOther___rarg(x_1688, x_1689, x_2, x_1681);
lean_dec(x_2);
return x_1690;
}
else
{
lean_object* x_1691; lean_object* x_1692; 
lean_dec(x_5);
x_1691 = lean_ctor_get(x_1679, 1);
lean_inc(x_1691);
lean_dec(x_1679);
x_1692 = lean_ctor_get(x_1680, 0);
lean_inc(x_1692);
lean_dec(x_1680);
x_1 = x_1692;
x_3 = x_1691;
goto _start;
}
}
else
{
uint8_t x_1694; 
lean_dec(x_5);
lean_dec(x_2);
x_1694 = !lean_is_exclusive(x_1679);
if (x_1694 == 0)
{
return x_1679;
}
else
{
lean_object* x_1695; lean_object* x_1696; lean_object* x_1697; 
x_1695 = lean_ctor_get(x_1679, 0);
x_1696 = lean_ctor_get(x_1679, 1);
lean_inc(x_1696);
lean_inc(x_1695);
lean_dec(x_1679);
x_1697 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1697, 0, x_1695);
lean_ctor_set(x_1697, 1, x_1696);
return x_1697;
}
}
}
else
{
lean_object* x_1698; 
x_1698 = l_Lean_ConstantInfo_value_x3f(x_1670);
lean_dec(x_1670);
if (lean_obj_tag(x_1698) == 0)
{
lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; 
lean_dec(x_1672);
lean_dec(x_1668);
lean_dec(x_1663);
lean_dec(x_1656);
x_1699 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1700 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1700, 0, x_1699);
x_1701 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1701, 0, x_1700);
x_1702 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__9;
x_1703 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1703, 0, x_1702);
lean_ctor_set(x_1703, 1, x_1701);
x_1704 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_1705 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1705, 0, x_1703);
lean_ctor_set(x_1705, 1, x_1704);
x_1706 = lean_box(0);
x_1707 = l_Lean_Meta_throwOther___rarg(x_1705, x_1706, x_2, x_1676);
lean_dec(x_2);
return x_1707;
}
else
{
lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; 
lean_dec(x_5);
x_1708 = lean_ctor_get(x_1698, 0);
lean_inc(x_1708);
lean_dec(x_1698);
x_1709 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_1708);
lean_inc(x_2);
x_1710 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_1709, x_2, x_1676);
if (lean_obj_tag(x_1710) == 0)
{
lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1752; lean_object* x_1753; 
x_1711 = lean_ctor_get(x_1710, 0);
lean_inc(x_1711);
x_1712 = lean_ctor_get(x_1710, 1);
lean_inc(x_1712);
lean_dec(x_1710);
x_1752 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__21;
lean_inc(x_2);
x_1753 = l_Lean_Meta_forallTelescope___rarg(x_1672, x_1752, x_2, x_1712);
if (lean_obj_tag(x_1753) == 0)
{
lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; uint8_t x_1758; lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; 
x_1754 = lean_ctor_get(x_1753, 0);
lean_inc(x_1754);
x_1755 = lean_ctor_get(x_1753, 1);
lean_inc(x_1755);
lean_dec(x_1753);
lean_inc(x_1668);
x_1756 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1756, 0, x_1668);
lean_ctor_set(x_1756, 1, x_1666);
lean_ctor_set(x_1756, 2, x_1754);
x_1757 = lean_box(0);
x_1758 = 0;
x_1759 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1759, 0, x_1756);
lean_ctor_set(x_1759, 1, x_1711);
lean_ctor_set(x_1759, 2, x_1757);
lean_ctor_set_uint8(x_1759, sizeof(void*)*3, x_1758);
x_1760 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1760, 0, x_1759);
x_1761 = lean_ctor_get(x_1755, 0);
lean_inc(x_1761);
x_1762 = l_Lean_Options_empty;
x_1763 = l_Lean_Environment_addAndCompile(x_1761, x_1762, x_1760);
lean_dec(x_1760);
if (lean_obj_tag(x_1763) == 0)
{
lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; lean_object* x_1771; uint8_t x_1772; 
lean_dec(x_1668);
lean_dec(x_1663);
lean_dec(x_1656);
x_1764 = lean_ctor_get(x_1763, 0);
lean_inc(x_1764);
lean_dec(x_1763);
x_1765 = l_Lean_KernelException_toMessageData(x_1764, x_1762);
x_1766 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_1765);
x_1767 = l_Lean_Format_pretty(x_1766, x_1762);
x_1768 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1768, 0, x_1767);
x_1769 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1769, 0, x_1768);
x_1770 = lean_box(0);
x_1771 = l_Lean_Meta_throwOther___rarg(x_1769, x_1770, x_2, x_1755);
lean_dec(x_2);
x_1772 = !lean_is_exclusive(x_1771);
if (x_1772 == 0)
{
return x_1771;
}
else
{
lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; 
x_1773 = lean_ctor_get(x_1771, 0);
x_1774 = lean_ctor_get(x_1771, 1);
lean_inc(x_1774);
lean_inc(x_1773);
lean_dec(x_1771);
x_1775 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1775, 0, x_1773);
lean_ctor_set(x_1775, 1, x_1774);
return x_1775;
}
}
else
{
lean_object* x_1776; 
x_1776 = lean_ctor_get(x_1763, 0);
lean_inc(x_1776);
lean_dec(x_1763);
x_1713 = x_1776;
x_1714 = x_1755;
goto block_1751;
}
}
else
{
uint8_t x_1777; 
lean_dec(x_1711);
lean_dec(x_1668);
lean_dec(x_1663);
lean_dec(x_1656);
lean_dec(x_2);
x_1777 = !lean_is_exclusive(x_1753);
if (x_1777 == 0)
{
return x_1753;
}
else
{
lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; 
x_1778 = lean_ctor_get(x_1753, 0);
x_1779 = lean_ctor_get(x_1753, 1);
lean_inc(x_1779);
lean_inc(x_1778);
lean_dec(x_1753);
x_1780 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1780, 0, x_1778);
lean_ctor_set(x_1780, 1, x_1779);
return x_1780;
}
}
block_1751:
{
lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; uint8_t x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; 
x_1715 = lean_mk_syntax_ident(x_1656);
x_1716 = l_Lean_mkOptionalNode___closed__2;
x_1717 = lean_array_push(x_1716, x_1715);
x_1718 = l_Lean_nullKind;
x_1719 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1719, 0, x_1718);
lean_ctor_set(x_1719, 1, x_1717);
x_1720 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
x_1721 = 1;
x_1722 = lean_box(0);
lean_inc(x_1668);
x_1723 = lean_add_attribute(x_1713, x_1668, x_1720, x_1719, x_1721, x_1722);
x_1724 = lean_box(0);
x_1725 = l_Lean_mkConst(x_1668, x_1724);
if (lean_obj_tag(x_1723) == 0)
{
lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; 
x_1738 = lean_ctor_get(x_1723, 0);
lean_inc(x_1738);
lean_dec(x_1723);
x_1739 = l_Lean_Meta_setEnv(x_1738, x_2, x_1714);
x_1740 = lean_ctor_get(x_1739, 1);
lean_inc(x_1740);
lean_dec(x_1739);
x_1726 = x_1740;
goto block_1737;
}
else
{
lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; uint8_t x_1747; 
lean_dec(x_1725);
lean_dec(x_1663);
x_1741 = lean_ctor_get(x_1723, 0);
lean_inc(x_1741);
lean_dec(x_1723);
x_1742 = lean_io_error_to_string(x_1741);
x_1743 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1743, 0, x_1742);
x_1744 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1744, 0, x_1743);
x_1745 = lean_box(0);
x_1746 = l_Lean_Meta_throwOther___rarg(x_1744, x_1745, x_2, x_1714);
lean_dec(x_2);
x_1747 = !lean_is_exclusive(x_1746);
if (x_1747 == 0)
{
return x_1746;
}
else
{
lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; 
x_1748 = lean_ctor_get(x_1746, 0);
x_1749 = lean_ctor_get(x_1746, 1);
lean_inc(x_1749);
lean_inc(x_1748);
lean_dec(x_1746);
x_1750 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1750, 0, x_1748);
lean_ctor_set(x_1750, 1, x_1749);
return x_1750;
}
}
block_1737:
{
lean_object* x_1727; 
lean_inc(x_2);
lean_inc(x_1725);
x_1727 = l_Lean_Meta_inferType(x_1725, x_2, x_1726);
if (lean_obj_tag(x_1727) == 0)
{
lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; 
x_1728 = lean_ctor_get(x_1727, 0);
lean_inc(x_1728);
x_1729 = lean_ctor_get(x_1727, 1);
lean_inc(x_1729);
lean_dec(x_1727);
x_1730 = l_Lean_mkAppStx___closed__2;
x_1731 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__32___boxed), 8, 4);
lean_closure_set(x_1731, 0, x_1673);
lean_closure_set(x_1731, 1, x_1730);
lean_closure_set(x_1731, 2, x_1663);
lean_closure_set(x_1731, 3, x_1725);
x_1732 = l_Lean_Meta_forallTelescope___rarg(x_1728, x_1731, x_2, x_1729);
return x_1732;
}
else
{
uint8_t x_1733; 
lean_dec(x_1725);
lean_dec(x_1663);
lean_dec(x_2);
x_1733 = !lean_is_exclusive(x_1727);
if (x_1733 == 0)
{
return x_1727;
}
else
{
lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; 
x_1734 = lean_ctor_get(x_1727, 0);
x_1735 = lean_ctor_get(x_1727, 1);
lean_inc(x_1735);
lean_inc(x_1734);
lean_dec(x_1727);
x_1736 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1736, 0, x_1734);
lean_ctor_set(x_1736, 1, x_1735);
return x_1736;
}
}
}
}
}
else
{
uint8_t x_1781; 
lean_dec(x_1672);
lean_dec(x_1668);
lean_dec(x_1663);
lean_dec(x_1656);
lean_dec(x_2);
x_1781 = !lean_is_exclusive(x_1710);
if (x_1781 == 0)
{
return x_1710;
}
else
{
lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; 
x_1782 = lean_ctor_get(x_1710, 0);
x_1783 = lean_ctor_get(x_1710, 1);
lean_inc(x_1783);
lean_inc(x_1782);
lean_dec(x_1710);
x_1784 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1784, 0, x_1782);
lean_ctor_set(x_1784, 1, x_1783);
return x_1784;
}
}
}
}
}
else
{
uint8_t x_1785; 
lean_dec(x_1672);
lean_dec(x_1670);
lean_dec(x_1668);
lean_dec(x_1663);
lean_dec(x_1656);
lean_dec(x_5);
lean_dec(x_2);
x_1785 = !lean_is_exclusive(x_1674);
if (x_1785 == 0)
{
return x_1674;
}
else
{
lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; 
x_1786 = lean_ctor_get(x_1674, 0);
x_1787 = lean_ctor_get(x_1674, 1);
lean_inc(x_1787);
lean_inc(x_1786);
lean_dec(x_1674);
x_1788 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1788, 0, x_1786);
lean_ctor_set(x_1788, 1, x_1787);
return x_1788;
}
}
}
else
{
uint8_t x_1789; 
lean_dec(x_1668);
lean_dec(x_1663);
lean_dec(x_1656);
lean_dec(x_5);
lean_dec(x_2);
x_1789 = !lean_is_exclusive(x_1669);
if (x_1789 == 0)
{
return x_1669;
}
else
{
lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; 
x_1790 = lean_ctor_get(x_1669, 0);
x_1791 = lean_ctor_get(x_1669, 1);
lean_inc(x_1791);
lean_inc(x_1790);
lean_dec(x_1669);
x_1792 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1792, 0, x_1790);
lean_ctor_set(x_1792, 1, x_1791);
return x_1792;
}
}
}
else
{
lean_object* x_1793; lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; 
lean_dec(x_1656);
lean_dec(x_5);
x_1793 = lean_ctor_get(x_1666, 0);
lean_inc(x_1793);
lean_dec(x_1666);
x_1794 = lean_box(0);
x_1795 = l_Lean_mkConst(x_1793, x_1794);
lean_inc(x_2);
lean_inc(x_1795);
x_1796 = l_Lean_Meta_inferType(x_1795, x_2, x_1643);
if (lean_obj_tag(x_1796) == 0)
{
lean_object* x_1797; lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; 
x_1797 = lean_ctor_get(x_1796, 0);
lean_inc(x_1797);
x_1798 = lean_ctor_get(x_1796, 1);
lean_inc(x_1798);
lean_dec(x_1796);
x_1799 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___lambda__34___boxed), 6, 2);
lean_closure_set(x_1799, 0, x_1663);
lean_closure_set(x_1799, 1, x_1795);
x_1800 = l_Lean_Meta_forallTelescope___rarg(x_1797, x_1799, x_2, x_1798);
return x_1800;
}
else
{
uint8_t x_1801; 
lean_dec(x_1795);
lean_dec(x_1663);
lean_dec(x_2);
x_1801 = !lean_is_exclusive(x_1796);
if (x_1801 == 0)
{
return x_1796;
}
else
{
lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; 
x_1802 = lean_ctor_get(x_1796, 0);
x_1803 = lean_ctor_get(x_1796, 1);
lean_inc(x_1803);
lean_inc(x_1802);
lean_dec(x_1796);
x_1804 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1804, 0, x_1802);
lean_ctor_set(x_1804, 1, x_1803);
return x_1804;
}
}
}
}
else
{
lean_object* x_1805; 
lean_dec(x_1644);
x_1805 = lean_box(0);
x_1645 = x_1805;
goto block_1655;
}
block_1655:
{
lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; 
lean_dec(x_1645);
x_1646 = lean_expr_dbg_to_string(x_5);
lean_dec(x_5);
x_1647 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1647, 0, x_1646);
x_1648 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1648, 0, x_1647);
x_1649 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___closed__3;
x_1650 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1650, 0, x_1649);
lean_ctor_set(x_1650, 1, x_1648);
x_1651 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_1652 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1652, 0, x_1650);
lean_ctor_set(x_1652, 1, x_1651);
x_1653 = lean_box(0);
x_1654 = l_Lean_Meta_throwOther___rarg(x_1652, x_1653, x_2, x_1643);
lean_dec(x_2);
return x_1654;
}
}
}
}
else
{
uint8_t x_1806; 
lean_dec(x_2);
x_1806 = !lean_is_exclusive(x_4);
if (x_1806 == 0)
{
return x_4;
}
else
{
lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; 
x_1807 = lean_ctor_get(x_4, 0);
x_1808 = lean_ctor_get(x_4, 1);
lean_inc(x_1808);
lean_inc(x_1807);
lean_dec(x_4);
x_1809 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1809, 0, x_1807);
lean_ctor_set(x_1809, 1, x_1808);
return x_1809;
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
lean_dec(x_1);
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParserBody_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody_x27(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_compile___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__9;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compile(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_Lean_MetavarContext_Inhabited___closed__1;
x_6 = l_Lean_Meta_run___rarg___closed__5;
x_7 = l_Lean_NameGenerator_Inhabited___closed__3;
x_8 = l_Lean_TraceState_Inhabited___closed__1;
x_9 = l_Std_PersistentArray_empty___closed__3;
x_10 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_7);
lean_ctor_set(x_10, 4, x_8);
lean_ctor_set(x_10, 5, x_9);
x_11 = l_Lean_Meta_addGlobalInstance___closed__3;
lean_inc(x_2);
x_12 = l_Lean_Meta_getConstInfo(x_2, x_11, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_ConstantInfo_value_x21(x_13);
lean_dec(x_13);
x_16 = l_Lean_PrettyPrinter_Parenthesizer_preprocessParserBody(x_15);
x_17 = l_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main(x_16, x_11, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 4);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Std_PersistentArray_forM___at_IO_runMeta___spec__3(x_22, x_4);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_28 = l_Lean_Name_append___main(x_2, x_27);
x_29 = lean_box(0);
x_30 = l_Lean_PrettyPrinter_Parenthesizer_compile___closed__1;
lean_inc(x_28);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_box(0);
x_33 = 0;
x_34 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_18);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Lean_Options_empty;
x_37 = l_Lean_Environment_addAndCompile(x_20, x_36, x_35);
lean_dec(x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_28);
lean_dec(x_2);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_KernelException_toMessageData(x_38, x_36);
x_40 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_39);
x_41 = l_Lean_Format_pretty(x_40, x_36);
x_42 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_42);
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_23);
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_mk_syntax_ident(x_2);
x_45 = l_Lean_mkOptionalNode___closed__2;
x_46 = lean_array_push(x_45, x_44);
x_47 = l_Lean_nullKind;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
if (x_3 == 0)
{
uint8_t x_49; lean_object* x_50; 
x_49 = 1;
lean_inc(x_48);
lean_inc(x_28);
x_50 = lean_add_attribute(x_43, x_28, x_27, x_48, x_49, x_25);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
x_54 = lean_add_attribute(x_51, x_28, x_53, x_48, x_49, x_52);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_48);
lean_dec(x_28);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_59 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__2;
x_60 = 1;
lean_inc(x_48);
lean_inc(x_28);
x_61 = lean_add_attribute(x_43, x_28, x_59, x_48, x_60, x_25);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
x_65 = lean_add_attribute(x_62, x_28, x_64, x_48, x_60, x_63);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_48);
lean_dec(x_28);
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
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_70 = lean_ctor_get(x_23, 1);
lean_inc(x_70);
lean_dec(x_23);
x_71 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__5;
x_72 = l_Lean_Name_append___main(x_2, x_71);
x_73 = lean_box(0);
x_74 = l_Lean_PrettyPrinter_Parenthesizer_compile___closed__1;
lean_inc(x_72);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
lean_ctor_set(x_75, 2, x_74);
x_76 = lean_box(0);
x_77 = 0;
x_78 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_18);
lean_ctor_set(x_78, 2, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*3, x_77);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = l_Lean_Options_empty;
x_81 = l_Lean_Environment_addAndCompile(x_20, x_80, x_79);
lean_dec(x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_72);
lean_dec(x_2);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l_Lean_KernelException_toMessageData(x_82, x_80);
x_84 = l_Lean_fmt___at_Lean_Message_toString___spec__1(x_83);
x_85 = l_Lean_Format_pretty(x_84, x_80);
x_86 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_70);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_81, 0);
lean_inc(x_88);
lean_dec(x_81);
x_89 = lean_mk_syntax_ident(x_2);
x_90 = l_Lean_mkOptionalNode___closed__2;
x_91 = lean_array_push(x_90, x_89);
x_92 = l_Lean_nullKind;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
if (x_3 == 0)
{
uint8_t x_94; lean_object* x_95; 
x_94 = 1;
lean_inc(x_93);
lean_inc(x_72);
x_95 = lean_add_attribute(x_88, x_72, x_71, x_93, x_94, x_70);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
x_99 = lean_add_attribute(x_96, x_72, x_98, x_93, x_94, x_97);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_93);
lean_dec(x_72);
x_100 = lean_ctor_get(x_95, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_102 = x_95;
} else {
 lean_dec_ref(x_95);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
else
{
lean_object* x_104; uint8_t x_105; lean_object* x_106; 
x_104 = l_Lean_PrettyPrinter_mkParenthesizerAttribute___closed__2;
x_105 = 1;
lean_inc(x_93);
lean_inc(x_72);
x_106 = lean_add_attribute(x_88, x_72, x_104, x_93, x_105, x_70);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2;
x_110 = lean_add_attribute(x_107, x_72, x_109, x_93, x_105, x_108);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_93);
lean_dec(x_72);
x_111 = lean_ctor_get(x_106, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_106, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_113 = x_106;
} else {
 lean_dec_ref(x_106);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_2);
x_115 = !lean_is_exclusive(x_23);
if (x_115 == 0)
{
return x_23;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_23, 0);
x_117 = lean_ctor_get(x_23, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_23);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_2);
x_119 = lean_ctor_get(x_17, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_17, 1);
lean_inc(x_120);
lean_dec(x_17);
x_121 = l_Lean_Meta_Exception_toStr(x_119);
x_122 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = lean_ctor_get(x_120, 4);
lean_inc(x_123);
lean_dec(x_120);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec(x_123);
x_125 = l_Std_PersistentArray_forM___at_IO_runMeta___spec__3(x_124, x_4);
lean_dec(x_124);
if (lean_obj_tag(x_125) == 0)
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_125, 0);
lean_dec(x_127);
lean_ctor_set_tag(x_125, 1);
lean_ctor_set(x_125, 0, x_122);
return x_125;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_122);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
else
{
uint8_t x_130; 
lean_dec(x_122);
x_130 = !lean_is_exclusive(x_125);
if (x_130 == 0)
{
return x_125;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_125, 0);
x_132 = lean_ctor_get(x_125, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_125);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_2);
x_134 = lean_ctor_get(x_12, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_12, 1);
lean_inc(x_135);
lean_dec(x_12);
x_136 = l_Lean_Meta_Exception_toStr(x_134);
x_137 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_138 = lean_ctor_get(x_135, 4);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec(x_138);
x_140 = l_Std_PersistentArray_forM___at_IO_runMeta___spec__3(x_139, x_4);
lean_dec(x_139);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_140, 0);
lean_dec(x_142);
lean_ctor_set_tag(x_140, 1);
lean_ctor_set(x_140, 0, x_137);
return x_140;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_137);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
else
{
uint8_t x_145; 
lean_dec(x_137);
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
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_PrettyPrinter_Parenthesizer_compile(x_1, x_2, x_5, x_4);
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
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TrailingParser");
return x_1;
}
}
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
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
x_16 = l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___closed__2;
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
uint8_t x_29; lean_object* x_30; 
lean_dec(x_2);
x_29 = 0;
lean_inc(x_1);
x_30 = l_Lean_PrettyPrinter_Parenthesizer_compile(x_3, x_1, x_29, x_4);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind), 5, 1);
lean_closure_set(x_33, 0, x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_30);
x_37 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind), 5, 1);
lean_closure_set(x_37, 0, x_1);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
uint8_t x_40; 
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
}
else
{
uint8_t x_44; lean_object* x_45; 
lean_dec(x_15);
lean_dec(x_2);
x_44 = 0;
lean_inc(x_1);
x_45 = l_Lean_PrettyPrinter_Parenthesizer_compile(x_3, x_1, x_44, x_4);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind), 5, 1);
lean_closure_set(x_48, 0, x_1);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_45, 0, x_49);
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_45, 0);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_45);
x_52 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind), 5, 1);
lean_closure_set(x_52, 0, x_1);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_45);
if (x_55 == 0)
{
return x_45;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_45, 0);
x_57 = lean_ctor_get(x_45, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_45);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
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
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantAux___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Parenthesizer_monadQuotation___spec__1___rarg___boxed), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
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
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed), 4, 3);
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
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed), 4, 3);
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
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed), 4, 3);
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
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed), 4, 3);
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
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed), 4, 3);
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
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main), 3, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_4, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
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
x_11 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_5, x_10, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 6, 2);
lean_closure_set(x_16, 0, x_9);
lean_closure_set(x_16, 1, x_15);
lean_ctor_set(x_13, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 6, 2);
lean_closure_set(x_19, 0, x_9);
lean_closure_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_25 = x_21;
} else {
 lean_dec_ref(x_21);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 6, 2);
lean_closure_set(x_26, 0, x_9);
lean_closure_set(x_26, 1, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
return x_6;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_6, 0);
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_6);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
case 1:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_dec(x_1);
x_39 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_37, x_2, x_3);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_38, x_43, x_41);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 6, 2);
lean_closure_set(x_49, 0, x_42);
lean_closure_set(x_49, 1, x_48);
lean_ctor_set(x_46, 0, x_49);
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_46);
x_52 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 6, 2);
lean_closure_set(x_52, 0, x_42);
lean_closure_set(x_52, 1, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_44, 0, x_53);
return x_44;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_44, 0);
x_55 = lean_ctor_get(x_44, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_44);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_58 = x_54;
} else {
 lean_dec_ref(x_54);
 x_58 = lean_box(0);
}
x_59 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 6, 2);
lean_closure_set(x_59, 0, x_42);
lean_closure_set(x_59, 1, x_56);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_55);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_42);
x_62 = !lean_is_exclusive(x_44);
if (x_62 == 0)
{
return x_44;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_44, 0);
x_64 = lean_ctor_get(x_44, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_44);
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
lean_dec(x_38);
x_66 = !lean_is_exclusive(x_39);
if (x_66 == 0)
{
return x_39;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_39, 0);
x_68 = lean_ctor_get(x_39, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_39);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
case 2:
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_1, 0);
lean_inc(x_70);
lean_dec(x_1);
x_71 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_70, x_2, x_3);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_optional_parenthesizer), 5, 1);
lean_closure_set(x_76, 0, x_75);
lean_ctor_set(x_73, 0, x_76);
return x_71;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_73, 0);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_73);
x_79 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_optional_parenthesizer), 5, 1);
lean_closure_set(x_79, 0, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
lean_ctor_set(x_71, 0, x_80);
return x_71;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_81 = lean_ctor_get(x_71, 0);
x_82 = lean_ctor_get(x_71, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_71);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_85 = x_81;
} else {
 lean_dec_ref(x_81);
 x_85 = lean_box(0);
}
x_86 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_optional_parenthesizer), 5, 1);
lean_closure_set(x_86, 0, x_83);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_82);
return x_88;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_71);
if (x_89 == 0)
{
return x_71;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_71, 0);
x_91 = lean_ctor_get(x_71, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_71);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
case 3:
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_1, 0);
lean_inc(x_93);
lean_dec(x_1);
x_94 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_93, x_2, x_3);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer), 5, 1);
lean_closure_set(x_99, 0, x_98);
lean_ctor_set(x_96, 0, x_99);
return x_94;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_96, 0);
x_101 = lean_ctor_get(x_96, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_96);
x_102 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer), 5, 1);
lean_closure_set(x_102, 0, x_100);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
lean_ctor_set(x_94, 0, x_103);
return x_94;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_104 = lean_ctor_get(x_94, 0);
x_105 = lean_ctor_get(x_94, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_94);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_108 = x_104;
} else {
 lean_dec_ref(x_104);
 x_108 = lean_box(0);
}
x_109 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer), 5, 1);
lean_closure_set(x_109, 0, x_106);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_105);
return x_111;
}
}
else
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_94);
if (x_112 == 0)
{
return x_94;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_94, 0);
x_114 = lean_ctor_get(x_94, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_94);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
case 4:
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_1, 0);
lean_inc(x_116);
lean_dec(x_1);
x_117 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_116, x_2, x_3);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_119, 0);
x_122 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_try_parenthesizer), 5, 1);
lean_closure_set(x_122, 0, x_121);
lean_ctor_set(x_119, 0, x_122);
return x_117;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_119, 0);
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_119);
x_125 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_try_parenthesizer), 5, 1);
lean_closure_set(x_125, 0, x_123);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
lean_ctor_set(x_117, 0, x_126);
return x_117;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_127 = lean_ctor_get(x_117, 0);
x_128 = lean_ctor_get(x_117, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_117);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_131 = x_127;
} else {
 lean_dec_ref(x_127);
 x_131 = lean_box(0);
}
x_132 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_try_parenthesizer), 5, 1);
lean_closure_set(x_132, 0, x_129);
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_130);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_128);
return x_134;
}
}
else
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_117);
if (x_135 == 0)
{
return x_117;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_117, 0);
x_137 = lean_ctor_get(x_117, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_117);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
case 5:
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_1, 0);
lean_inc(x_139);
lean_dec(x_1);
x_140 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_139, x_2, x_3);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_140, 0);
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer), 5, 1);
lean_closure_set(x_145, 0, x_144);
lean_ctor_set(x_142, 0, x_145);
return x_140;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_142, 0);
x_147 = lean_ctor_get(x_142, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_142);
x_148 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer), 5, 1);
lean_closure_set(x_148, 0, x_146);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
lean_ctor_set(x_140, 0, x_149);
return x_140;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_150 = lean_ctor_get(x_140, 0);
x_151 = lean_ctor_get(x_140, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_140);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_154 = x_150;
} else {
 lean_dec_ref(x_150);
 x_154 = lean_box(0);
}
x_155 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_many_parenthesizer), 5, 1);
lean_closure_set(x_155, 0, x_152);
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_154;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_151);
return x_157;
}
}
else
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_140);
if (x_158 == 0)
{
return x_140;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_140, 0);
x_160 = lean_ctor_get(x_140, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_140);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
case 6:
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_1, 0);
lean_inc(x_162);
lean_dec(x_1);
x_163 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_162, x_2, x_3);
if (lean_obj_tag(x_163) == 0)
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; uint8_t x_166; 
x_165 = lean_ctor_get(x_163, 0);
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_165, 0);
x_168 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_many1_parenthesizer), 5, 1);
lean_closure_set(x_168, 0, x_167);
lean_ctor_set(x_165, 0, x_168);
return x_163;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_169 = lean_ctor_get(x_165, 0);
x_170 = lean_ctor_get(x_165, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_165);
x_171 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_many1_parenthesizer), 5, 1);
lean_closure_set(x_171, 0, x_169);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
lean_ctor_set(x_163, 0, x_172);
return x_163;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_173 = lean_ctor_get(x_163, 0);
x_174 = lean_ctor_get(x_163, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_163);
x_175 = lean_ctor_get(x_173, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_177 = x_173;
} else {
 lean_dec_ref(x_173);
 x_177 = lean_box(0);
}
x_178 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_many1_parenthesizer), 5, 1);
lean_closure_set(x_178, 0, x_175);
if (lean_is_scalar(x_177)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_177;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_176);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_174);
return x_180;
}
}
else
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_163);
if (x_181 == 0)
{
return x_163;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_163, 0);
x_183 = lean_ctor_get(x_163, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_163);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
case 7:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_1, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_1, 1);
lean_inc(x_186);
lean_dec(x_1);
x_187 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_185, x_2, x_3);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
lean_dec(x_188);
x_192 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_186, x_191, x_189);
if (lean_obj_tag(x_192) == 0)
{
uint8_t x_193; 
x_193 = !lean_is_exclusive(x_192);
if (x_193 == 0)
{
lean_object* x_194; uint8_t x_195; 
x_194 = lean_ctor_get(x_192, 0);
x_195 = !lean_is_exclusive(x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_194, 0);
x_197 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer), 6, 2);
lean_closure_set(x_197, 0, x_190);
lean_closure_set(x_197, 1, x_196);
lean_ctor_set(x_194, 0, x_197);
return x_192;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_194, 0);
x_199 = lean_ctor_get(x_194, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_194);
x_200 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer), 6, 2);
lean_closure_set(x_200, 0, x_190);
lean_closure_set(x_200, 1, x_198);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
lean_ctor_set(x_192, 0, x_201);
return x_192;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_202 = lean_ctor_get(x_192, 0);
x_203 = lean_ctor_get(x_192, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_192);
x_204 = lean_ctor_get(x_202, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_206 = x_202;
} else {
 lean_dec_ref(x_202);
 x_206 = lean_box(0);
}
x_207 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_sepBy_parenthesizer), 6, 2);
lean_closure_set(x_207, 0, x_190);
lean_closure_set(x_207, 1, x_204);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_205);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_203);
return x_209;
}
}
else
{
uint8_t x_210; 
lean_dec(x_190);
x_210 = !lean_is_exclusive(x_192);
if (x_210 == 0)
{
return x_192;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_192, 0);
x_212 = lean_ctor_get(x_192, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_192);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_186);
x_214 = !lean_is_exclusive(x_187);
if (x_214 == 0)
{
return x_187;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_187, 0);
x_216 = lean_ctor_get(x_187, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_187);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
case 8:
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_1, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_1, 1);
lean_inc(x_219);
lean_dec(x_1);
x_220 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_218, x_2, x_3);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_ctor_get(x_221, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
lean_dec(x_221);
x_225 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_219, x_224, x_222);
if (lean_obj_tag(x_225) == 0)
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_225);
if (x_226 == 0)
{
lean_object* x_227; uint8_t x_228; 
x_227 = lean_ctor_get(x_225, 0);
x_228 = !lean_is_exclusive(x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_227, 0);
x_230 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_sepBy1_parenthesizer), 6, 2);
lean_closure_set(x_230, 0, x_223);
lean_closure_set(x_230, 1, x_229);
lean_ctor_set(x_227, 0, x_230);
return x_225;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_231 = lean_ctor_get(x_227, 0);
x_232 = lean_ctor_get(x_227, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_227);
x_233 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_sepBy1_parenthesizer), 6, 2);
lean_closure_set(x_233, 0, x_223);
lean_closure_set(x_233, 1, x_231);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_232);
lean_ctor_set(x_225, 0, x_234);
return x_225;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_235 = lean_ctor_get(x_225, 0);
x_236 = lean_ctor_get(x_225, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_225);
x_237 = lean_ctor_get(x_235, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_239 = x_235;
} else {
 lean_dec_ref(x_235);
 x_239 = lean_box(0);
}
x_240 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_sepBy1_parenthesizer), 6, 2);
lean_closure_set(x_240, 0, x_223);
lean_closure_set(x_240, 1, x_237);
if (lean_is_scalar(x_239)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_239;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_238);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_236);
return x_242;
}
}
else
{
uint8_t x_243; 
lean_dec(x_223);
x_243 = !lean_is_exclusive(x_225);
if (x_243 == 0)
{
return x_225;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_225, 0);
x_245 = lean_ctor_get(x_225, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_225);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
else
{
uint8_t x_247; 
lean_dec(x_219);
x_247 = !lean_is_exclusive(x_220);
if (x_247 == 0)
{
return x_220;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_220, 0);
x_249 = lean_ctor_get(x_220, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_220);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
case 9:
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_251 = lean_ctor_get(x_1, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_1, 1);
lean_inc(x_252);
x_253 = lean_ctor_get(x_1, 2);
lean_inc(x_253);
lean_dec(x_1);
x_254 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_253, x_2, x_3);
if (lean_obj_tag(x_254) == 0)
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_254);
if (x_255 == 0)
{
lean_object* x_256; uint8_t x_257; 
x_256 = lean_ctor_get(x_254, 0);
x_257 = !lean_is_exclusive(x_256);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_256, 0);
x_259 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 7, 3);
lean_closure_set(x_259, 0, x_251);
lean_closure_set(x_259, 1, x_252);
lean_closure_set(x_259, 2, x_258);
lean_ctor_set(x_256, 0, x_259);
return x_254;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_260 = lean_ctor_get(x_256, 0);
x_261 = lean_ctor_get(x_256, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_256);
x_262 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 7, 3);
lean_closure_set(x_262, 0, x_251);
lean_closure_set(x_262, 1, x_252);
lean_closure_set(x_262, 2, x_260);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_261);
lean_ctor_set(x_254, 0, x_263);
return x_254;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_264 = lean_ctor_get(x_254, 0);
x_265 = lean_ctor_get(x_254, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_254);
x_266 = lean_ctor_get(x_264, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_264, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_268 = x_264;
} else {
 lean_dec_ref(x_264);
 x_268 = lean_box(0);
}
x_269 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer), 7, 3);
lean_closure_set(x_269, 0, x_251);
lean_closure_set(x_269, 1, x_252);
lean_closure_set(x_269, 2, x_266);
if (lean_is_scalar(x_268)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_268;
}
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_267);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_265);
return x_271;
}
}
else
{
uint8_t x_272; 
lean_dec(x_252);
lean_dec(x_251);
x_272 = !lean_is_exclusive(x_254);
if (x_272 == 0)
{
return x_254;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_254, 0);
x_274 = lean_ctor_get(x_254, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_254);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
return x_275;
}
}
}
case 10:
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_1, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_1, 1);
lean_inc(x_277);
x_278 = lean_ctor_get(x_1, 2);
lean_inc(x_278);
lean_dec(x_1);
x_279 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main(x_278, x_2, x_3);
if (lean_obj_tag(x_279) == 0)
{
uint8_t x_280; 
x_280 = !lean_is_exclusive(x_279);
if (x_280 == 0)
{
lean_object* x_281; uint8_t x_282; 
x_281 = lean_ctor_get(x_279, 0);
x_282 = !lean_is_exclusive(x_281);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_281, 0);
x_284 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer), 7, 3);
lean_closure_set(x_284, 0, x_276);
lean_closure_set(x_284, 1, x_277);
lean_closure_set(x_284, 2, x_283);
lean_ctor_set(x_281, 0, x_284);
return x_279;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_285 = lean_ctor_get(x_281, 0);
x_286 = lean_ctor_get(x_281, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_281);
x_287 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer), 7, 3);
lean_closure_set(x_287, 0, x_276);
lean_closure_set(x_287, 1, x_277);
lean_closure_set(x_287, 2, x_285);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_286);
lean_ctor_set(x_279, 0, x_288);
return x_279;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_289 = lean_ctor_get(x_279, 0);
x_290 = lean_ctor_get(x_279, 1);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_279);
x_291 = lean_ctor_get(x_289, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_289, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_293 = x_289;
} else {
 lean_dec_ref(x_289);
 x_293 = lean_box(0);
}
x_294 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer), 7, 3);
lean_closure_set(x_294, 0, x_276);
lean_closure_set(x_294, 1, x_277);
lean_closure_set(x_294, 2, x_291);
if (lean_is_scalar(x_293)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_293;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_292);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_290);
return x_296;
}
}
else
{
uint8_t x_297; 
lean_dec(x_277);
lean_dec(x_276);
x_297 = !lean_is_exclusive(x_279);
if (x_297 == 0)
{
return x_279;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_279, 0);
x_299 = lean_ctor_get(x_279, 1);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_279);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
return x_300;
}
}
}
case 11:
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_1);
x_301 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__1;
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_2);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_3);
return x_303;
}
case 12:
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_1);
x_304 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__2;
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_2);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_3);
return x_306;
}
case 13:
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__6;
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_2);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_3);
return x_309;
}
case 14:
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__10;
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_2);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_3);
return x_312;
}
case 15:
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__14;
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_2);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_3);
return x_315;
}
case 16:
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__18;
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_2);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_3);
return x_318;
}
case 17:
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__22;
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_2);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_3);
return x_321;
}
case 18:
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_322 = lean_ctor_get(x_1, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_1, 1);
lean_inc(x_323);
lean_dec(x_1);
x_324 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___boxed), 6, 2);
lean_closure_set(x_324, 0, x_322);
lean_closure_set(x_324, 1, x_323);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_2);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_3);
return x_326;
}
default: 
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_1, 0);
lean_inc(x_327);
lean_dec(x_1);
x_328 = l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr___main___closed__23;
x_329 = l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe(x_327, x_328, x_2, x_3);
return x_329;
}
}
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
lean_object* _init_l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_compileParenthesizerDescr), 3, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant___closed__1;
lean_inc(x_2);
x_5 = l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe(x_2, x_4, x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_Lean_PrettyPrinter_parenthesizerAttribute;
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_10, x_2, x_8, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_9);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_9);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_5);
if (x_20 == 0)
{
return x_5;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_5);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
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
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___boxed), 6, 2);
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
lean_object* l___private_Lean_PrettyPrinter_Parenthesizer_1__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__5;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta(lean_object*);
lean_object* initialize_Lean_KeyedDeclsAttribute(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_PrettyPrinter_Parenthesizer(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_KeyedDeclsAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_mkParenthesizerAttribute___lambda__1___closed__1);
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
l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__1 = _init_l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__1);
l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2 = _init_l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__2);
l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__3 = _init_l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__3);
l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__4 = _init_l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__4);
l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__5 = _init_l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__5);
l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__6 = _init_l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCombinatorParenthesizerAttribute___closed__6);
l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__3 = _init_l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__3();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__3);
l_Lean_SMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__1___closed__1 = _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__1___closed__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__1___closed__1);
l_Lean_SMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__1___closed__2 = _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__1___closed__2();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__1___closed__2);
l_Lean_SMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__1 = _init_l_Lean_SMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_PrettyPrinter_combinatorParenthesizerAttribute___spec__1);
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
l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__5 = _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__5);
l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__6 = _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__6);
l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__5 = _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__5);
l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__6 = _init_l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___closed__6);
l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4 = _init_l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4);
l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___lambda__1___closed__3);
l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___closed__2);
l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___closed__3 = _init_l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_levelParser_parenthesizer___closed__3);
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
l_Lean_PrettyPrinter_Parenthesizer_compile___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_compile___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_compile___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___closed__1);
l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___closed__2 = _init_l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_mkParenthesizerOfConstantUnsafe___closed__2);
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
l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant___closed__1 = _init_l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Parenthesizer_addParenthesizerFromConstant___closed__1);
l_Lean_PrettyPrinter_parenthesizeTerm___closed__1 = _init_l_Lean_PrettyPrinter_parenthesizeTerm___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizeTerm___closed__1);
l_Lean_PrettyPrinter_parenthesizeCommand___closed__1 = _init_l_Lean_PrettyPrinter_parenthesizeCommand___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizeCommand___closed__1);
l_Lean_PrettyPrinter_parenthesizeCommand___closed__2 = _init_l_Lean_PrettyPrinter_parenthesizeCommand___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizeCommand___closed__2);
l_Lean_PrettyPrinter_parenthesizeCommand___closed__3 = _init_l_Lean_PrettyPrinter_parenthesizeCommand___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_parenthesizeCommand___closed__3);
res = l___private_Lean_PrettyPrinter_Parenthesizer_1__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
