// Lean compiler output
// Module: Lean.Elab.BuiltinNotation
// Imports: Init Init.Data.ToString Lean.Compiler.BorrowedAnnotation Lean.Meta.KAbstract Lean.Elab.Term Lean.Elab.SyntheticMVars
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
lean_object* l_Lean_Elab_Term_expandHave_match__3(lean_object*);
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__26;
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabParserMacro(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__4;
extern lean_object* l_Lean_Meta_reduceNative_x3f___closed__2;
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg___closed__2;
lean_object* l_Lean_Meta_mkExpectedTypeHint___at_Lean_Elab_Term_elabNativeDecide___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkPairs_loop___closed__5;
lean_object* l_Lean_Elab_Term_expandSuffices_match__2(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_instReprOption___rarg___closed__1;
lean_object* l_Lean_Meta_mkEqRefl___at_Lean_Elab_Term_elabNativeRefl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
extern lean_object* l_termIf__Then__Else_____closed__2;
lean_object* l_Lean_Elab_Term_expandSuffices_match__5___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_let_x21___closed__1;
lean_object* l_Lean_Elab_Term_expandHave_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandHave___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__4;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabNativeRefl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__36;
lean_object* l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__1;
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__2;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__2;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11900____closed__13;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
extern lean_object* l_Lean_Parser_Tactic_have___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_Term_expandCDot_x3f_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_expandHave___closed__1;
lean_object* l_Lean_Elab_Term_elabSubst_match__1___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandAssert___closed__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__31;
extern lean_object* l_termIf_____x3a__Then__Else_____closed__3;
lean_object* l_Lean_Elab_Term_expandHave___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__3;
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_911____closed__4;
lean_object* l_Lean_Elab_Term_getDeclName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__6;
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13394____closed__6;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11370____closed__13;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__1;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_show___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__3;
lean_object* l_Lean_Elab_Term_elabParen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instToExprBool___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_expandSuffices_match__7(lean_object*);
lean_object* l_Lean_Meta_mkEq___at_Lean_Elab_Term_elabNativeRefl___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__3;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12817____closed__10;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_subst___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_unreachable___elambda__1___closed__2;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__1(lean_object*);
extern lean_object* l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__12;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Elab_Term_expandAssert_match__1(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__8;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__19;
lean_object* l_Lean_Elab_Term_elabTermAndSynthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__5;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__3;
extern lean_object* l_Lean_Parser_Term_fromTerm___elambda__1___closed__2;
lean_object* l_Lean_Meta_mkDecide___at_Lean_Elab_Term_elabNativeDecide___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNativeDecide___rarg___closed__1;
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_23____closed__7;
lean_object* l_Lean_Elab_Term_elabNativeRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instReprBool___closed__1;
extern lean_object* l_termS_x21_____closed__3;
extern lean_object* l_Lean_Parser_Term_nativeDecide___elambda__1___closed__2;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_parser_x21___elambda__1___closed__2;
extern lean_object* l_Lean_Meta_mkAppM___rarg___closed__2;
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__1;
lean_object* l_Lean_Elab_Term_elabParen___closed__3;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11370____closed__12;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___closed__5;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__11;
extern lean_object* l_Lean_interpolatedStrKind;
lean_object* l___regBuiltin_Lean_Elab_Term_elabSubst___closed__1;
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__9;
lean_object* l_Lean_Elab_Term_mkPairs_loop___closed__2;
lean_object* l_Lean_Elab_Term_elabSubst___closed__7;
lean_object* l_Lean_Elab_Term_elabPanic___closed__6;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1989____closed__4;
lean_object* l___regBuiltin_Lean_Elab_Term_elabParen(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_elabSubst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandDbgTrace___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandHave_match__4(lean_object*);
lean_object* l_Lean_Elab_Term_mkPairs_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__9;
lean_object* l_Lean_Elab_Term_mkAuxName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1192____closed__8;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkEqRefl___at_Lean_Elab_Term_elabNativeDecide___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__39;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Term_expandSuffices_match__6___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__2;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Elab_Term_elabNativeRefl___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_tupleTail___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__35;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__6;
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__4;
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__2;
lean_object* l_Lean_Elab_Term_expandShow___closed__1;
lean_object* l_Lean_Elab_Term_expandSorry___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__18;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__30;
extern lean_object* l_termS_x21_____closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandShow___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_14986____closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16;
lean_object* l_Lean_Elab_Term_expandAssert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSorry___rarg___closed__7;
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNativeRefl_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___closed__3;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__2;
lean_object* l_Lean_Elab_Term_mkPairs_loop___closed__4;
lean_object* l_Lean_Elab_Term_elabParen___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__7;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_elabParen___closed__1;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__2(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabTParserMacro(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__10;
lean_object* l_Lean_Elab_Term_expandShow___closed__2;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_byTactic___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_expandAssert_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__24;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandHave(lean_object*);
lean_object* l_Lean_Syntax_SepArray_getElems___rarg(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabPanic(lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__6;
lean_object* l_Lean_Elab_Term_expandSuffices_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20;
extern lean_object* l_Lean_Parser_Term_emptyC___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__3;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__10;
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__32;
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_911____closed__3;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTParserMacro___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_suffices___elambda__1___closed__1;
extern lean_object* l_Lean_setOptionFromString___closed__4;
lean_object* l_Lean_Elab_Term_elabNativeRefl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__3;
lean_object* l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__6;
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_16359____closed__2;
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__5;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandHave___closed__1;
lean_object* l_Lean_Elab_Term_elabNativeDecide(lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabNativeRefl___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandShow___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instQuoteProd___rarg___closed__2;
lean_object* l_Lean_Elab_Term_expandDbgTrace(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11900____closed__14;
lean_object* l_Lean_Meta_mkExpectedTypeHint___at_Lean_Elab_Term_elabNativeRefl___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkPairs_loop___closed__1;
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabSubst___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint___at_Lean_Elab_Term_elabNativeRefl___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__10;
lean_object* l_Lean_Meta_mkDecide___at_Lean_Elab_Term_elabNativeDecide___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_tparser_x21___elambda__1___closed__2;
extern lean_object* l_Lean_Meta_mkDecide___rarg___closed__1;
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__5;
lean_object* l_Lean_Elab_Term_expandHave_match__1(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__1;
extern lean_object* l_Lean_Parser_Term_macroDollarArg___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandUnreachable(lean_object*);
lean_object* l_Lean_Elab_Term_mkInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandEmptyC___closed__1;
lean_object* l_Lean_Elab_Term_expandSuffices_match__3___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkArrow___closed__2;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabDecide___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandShow___closed__3;
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSorry___rarg___closed__3;
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__5;
lean_object* l_Lean_Elab_getRefPosition___at_Lean_Elab_Term_elabPanic___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM___at_Lean_Elab_Term_elabStateRefT___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__4;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_expandSorry___rarg___closed__5;
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__6;
lean_object* l_Lean_Elab_Term_elabTParserMacro___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandSuffices(lean_object*);
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabDecide(lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__5;
lean_object* l_Lean_Meta_mkEqRefl___at_Lean_Elab_Term_elabNativeRefl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_mkPairs_loop___closed__3;
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__3;
extern lean_object* l_Lean_strLitKind___closed__2;
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__1;
lean_object* l_Lean_throwError___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instQuoteBool___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__7;
lean_object* l_Lean_Elab_Term_expandSuffices_match__6(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Elab_Term_elabSubst___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNativeDecide(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSourceInfo___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux_match__1(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13394____closed__11;
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabParen___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11370____closed__10;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_maxPrec;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabNativeRefl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__2;
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSuffices_match__8(lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandShow(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__21;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__38;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__3;
lean_object* l___private_Init_Meta_0__Lean_quoteName(lean_object*);
lean_object* l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSorry___rarg___closed__6;
extern lean_object* l_Lean_Literal_type___closed__2;
extern lean_object* l_Lean_Parser_Term_have___elambda__1___closed__1;
extern lean_object* l_Lean_instToExprUnit___lambda__1___closed__3;
lean_object* l_Lean_Elab_Term_expandHave_match__2(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandDbgTrace___closed__1;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst_match__1(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__6;
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
lean_object* l_Lean_Meta_mkEqRefl___at_Lean_Elab_Term_elabNativeDecide___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__8;
extern lean_object* l_Lean_instInhabitedSyntax;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandHave_match__4___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_dbgTrace___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_elabSubst___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSuffices___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabDecide___rarg___closed__1;
lean_object* l_Lean_Elab_Term_elabPanic___closed__11;
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabBorrowed(lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAssert___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12817____closed__8;
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__4;
lean_object* l___regBuiltin_Lean_Elab_Term_expandEmptyC(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_Syntax_mkAntiquotNode___closed__9;
lean_object* l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_elabSubst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabDecide___boxed(lean_object*);
extern lean_object* l_term___x2b_x2b_____closed__2;
extern lean_object* l_Lean_Parser_Term_cdot___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__4;
lean_object* l_Lean_Elab_Term_elabSubst___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabParserMacro___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__1;
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__7;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__2;
lean_object* l_Lean_Elab_Term_elabStateRefT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabDecide___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabNativeRefl(lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
uint8_t l_List_beq___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__2(lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_23____closed__13;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_dbgTrace___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instToExprBool___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabLetDeclAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandHave(lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot___boxed(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_mkApp___closed__1;
lean_object* l_Lean_Elab_Term_elabPanic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandHave_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTParserMacro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__3;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__1;
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__3;
lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNativeRefl_match__1(lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Elab_Term_elabSubst___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Elab_Term_elabSubst___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__7;
lean_object* l___regBuiltin_Lean_Elab_Term_expandShow(lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Elab_Term_elabParserMacro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
extern lean_object* l_Lean_instQuoteBool___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__5;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__28;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
lean_object* l_Lean_Elab_Term_expandSorry___boxed(lean_object*);
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_15_(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM___at_Lean_Elab_Term_elabStateRefT___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__5;
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__5;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__7;
lean_object* l_Lean_Elab_Term_expandSuffices_match__5(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_appendCore___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_23____closed__8;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__37;
lean_object* l___regBuiltin_Lean_Elab_Term_elabSubst(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___boxed__const__1;
lean_object* l___regBuiltin_Lean_Elab_Term_expandSorry(lean_object*);
lean_object* l_Lean_Elab_Term_expandSuffices_match__7___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__4;
lean_object* l_Lean_Elab_Term_elabPanic_match__1(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__15;
lean_object* l_Lean_Elab_Term_elabPanic___closed__12;
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot___spec__1(lean_object*, size_t, size_t);
lean_object* l_Lean_Elab_Term_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabSubst___spec__3(lean_object*);
extern lean_object* l_Lean_Syntax_expandInterpolatedStr___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_elabDecide(lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Meta_mkEq___at_Lean_Elab_Term_elabNativeRefl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSorry___rarg___closed__8;
lean_object* l_Lean_Elab_Term_elabNativeDecide___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_panic___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__17;
lean_object* l_Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSuffices_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__1;
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_14558____closed__3;
lean_object* l_Lean_Elab_Term_expandSuffices_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
extern lean_object* l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_elabParserMacro___closed__1;
extern lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1___closed__4;
extern lean_object* l_Lean_Parser_Term_borrowed___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabParserMacro___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__2;
lean_object* l_Lean_Elab_Term_expandSuffices_match__8___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withSynthesize___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkExpectedTypeHintImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__8;
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1___closed__2;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13394____closed__4;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__9;
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___closed__4;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__1;
lean_object* l_Lean_Elab_Term_elabSubst___closed__9;
lean_object* l_Lean_Elab_Term_elabPanic___closed__9;
extern lean_object* l_Lean_Meta_mkSorry___rarg___lambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_assert___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabPanic___closed__1;
extern lean_object* l_Lean_Parser_Tactic_show___closed__1;
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandShow___closed__4;
lean_object* l_Lean_Elab_Term_elabSubst___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandUnreachable___boxed(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__2;
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_14860____closed__2;
lean_object* l_Lean_Elab_Term_mkPairs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__7;
extern lean_object* l_prec_x28___x29___closed__7;
lean_object* l_Lean_Elab_Term_expandSorry___rarg___closed__2;
lean_object* l_Lean_Elab_Term_elabNativeDecide___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__8;
lean_object* l_Lean_Elab_Term_elabPanic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceNative_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_reduceNative_x3f___closed__4;
lean_object* l___regBuiltin_Lean_Elab_Term_elabParserMacro___closed__1;
lean_object* l_Lean_Elab_Term_mkPairs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__5;
lean_object* l_Lean_Elab_Term_expandSorry___rarg___closed__4;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot_match__1(lean_object*);
extern lean_object* l_prec_x28___x29___closed__3;
lean_object* l_Lean_Elab_Term_elabStateRefT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkPairs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabSubst___spec__3___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSuffices(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandSorry___closed__1;
lean_object* l_Lean_Elab_Term_expandSorry___rarg___closed__1;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Elab_Term_expandAssert___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Term_expandUnreachable(lean_object*);
lean_object* l_Lean_Elab_Term_expandSuffices_match__3(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__4;
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Elab_Term_elabSubst___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_nativeRefl___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabSubst___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_beq___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___closed__8;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__13;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__7;
extern lean_object* l_Lean_expandExplicitBindersAux_loop___closed__4;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandSuffices___closed__1;
lean_object* l_Lean_Elab_Term_expandEmptyC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__1;
lean_object* l_Lean_Elab_Term_expandHave_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfHasMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTParserMacro___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBorrowed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSuffices_match__4(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Term_elabPanic___closed__1;
extern lean_object* l_Lean_levelOne;
uint8_t l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandAssert(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot_match__1(lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_Elab_Term_expandSorry(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__2;
lean_object* l_Lean_Elab_Term_elabSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint___at_Lean_Elab_Term_elabNativeDecide___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandDbgTrace(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11370____closed__9;
lean_object* l_Lean_Elab_getRefPosition___at_Lean_Elab_Term_elabPanic___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__33;
lean_object* l___regBuiltin_Lean_Elab_Term_elabBorrowed___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabTParserMacro___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__5;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabStateRefT(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__4;
lean_object* l_Lean_throwError___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAssert___closed__1;
lean_object* l_Lean_Elab_Term_elabSubst_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11370____closed__8;
extern lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__8;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__3___rarg(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__34;
lean_object* l_Lean_Syntax_reprint(lean_object*);
lean_object* l_Lean_Elab_Term_expandCDot_x3f_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryPureCoe_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_stateRefT___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__4;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__8;
lean_object* l_Lean_Elab_Term_expandSuffices_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_expandAssert___closed__2;
lean_object* l_Lean_Elab_Term_elabSubst___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandCDot_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__1;
lean_object* l_Lean_markBorrowed(lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAssert___closed__4;
lean_object* l_Lean_Elab_Term_elabSubst___closed__1;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabAnonymousCtor_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabAnonymousCtor_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid constructor ⟨...⟩, expected type must be known");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabAnonymousCtor___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabAnonymousCtor___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid constructor ⟨...⟩, expected type must be an inductive type ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabAnonymousCtor___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid constructor ⟨...⟩, expected type must be an inductive type with only one constructor ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabAnonymousCtor___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabAnonymousCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_16 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Elab_Term_elabAnonymousCtor___closed__3;
x_19 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = l_Lean_Meta_whnf(x_21, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Expr_getAppFn(x_23);
if (lean_obj_tag(x_25) == 4)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_get(x_8, x_24);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_environment_find(x_30, x_26);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_32 = l_Lean_indentExpr(x_23);
x_33 = l_Lean_Elab_Term_elabAnonymousCtor___closed__5;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_KernelException_toMessageData___closed__15;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_37;
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_31, 0);
lean_inc(x_38);
lean_dec(x_31);
if (lean_obj_tag(x_38) == 5)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_39, 4);
lean_inc(x_40);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_41 = l_Lean_indentExpr(x_23);
x_42 = l_Lean_Elab_Term_elabAnonymousCtor___closed__7;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_KernelException_toMessageData___closed__15;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_23);
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_49 = lean_ctor_get(x_40, 0);
x_50 = lean_ctor_get(x_40, 1);
lean_dec(x_50);
x_51 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_7, x_8, x_29);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_52);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_54);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_mkCIdentFrom(x_1, x_49);
x_58 = l_Array_empty___closed__1;
x_59 = lean_array_push(x_58, x_57);
x_60 = l_Lean_Syntax_SepArray_getElems___rarg(x_15);
lean_dec(x_15);
x_61 = l_Array_appendCore___rarg(x_58, x_60);
lean_dec(x_60);
x_62 = l_Lean_nullKind___closed__2;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_array_push(x_59, x_63);
x_65 = l_myMacro____x40_Init_Notation___hyg_1989____closed__4;
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = !lean_is_exclusive(x_3);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_3, 3);
lean_inc(x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_66);
lean_ctor_set(x_40, 1, x_68);
lean_ctor_set(x_40, 0, x_69);
lean_ctor_set(x_3, 3, x_40);
x_70 = 1;
x_71 = l_Lean_Elab_Term_elabTerm(x_66, x_2, x_70, x_3, x_4, x_5, x_6, x_7, x_8, x_56);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_72 = lean_ctor_get(x_3, 0);
x_73 = lean_ctor_get(x_3, 1);
x_74 = lean_ctor_get(x_3, 2);
x_75 = lean_ctor_get(x_3, 3);
x_76 = lean_ctor_get(x_3, 4);
x_77 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_78 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_79 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_80 = lean_ctor_get(x_3, 5);
lean_inc(x_80);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_3);
lean_inc(x_66);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_66);
lean_ctor_set(x_40, 1, x_75);
lean_ctor_set(x_40, 0, x_81);
x_82 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_73);
lean_ctor_set(x_82, 2, x_74);
lean_ctor_set(x_82, 3, x_40);
lean_ctor_set(x_82, 4, x_76);
lean_ctor_set(x_82, 5, x_80);
lean_ctor_set_uint8(x_82, sizeof(void*)*6, x_77);
lean_ctor_set_uint8(x_82, sizeof(void*)*6 + 1, x_78);
lean_ctor_set_uint8(x_82, sizeof(void*)*6 + 2, x_79);
x_83 = 1;
x_84 = l_Lean_Elab_Term_elabTerm(x_66, x_2, x_83, x_82, x_4, x_5, x_6, x_7, x_8, x_56);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_85 = lean_ctor_get(x_40, 0);
lean_inc(x_85);
lean_dec(x_40);
x_86 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_7, x_8, x_29);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_87);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_89);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = l_Lean_mkCIdentFrom(x_1, x_85);
x_93 = l_Array_empty___closed__1;
x_94 = lean_array_push(x_93, x_92);
x_95 = l_Lean_Syntax_SepArray_getElems___rarg(x_15);
lean_dec(x_15);
x_96 = l_Array_appendCore___rarg(x_93, x_95);
lean_dec(x_95);
x_97 = l_Lean_nullKind___closed__2;
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_array_push(x_94, x_98);
x_100 = l_myMacro____x40_Init_Notation___hyg_1989____closed__4;
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = lean_ctor_get(x_3, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_3, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_3, 2);
lean_inc(x_104);
x_105 = lean_ctor_get(x_3, 3);
lean_inc(x_105);
x_106 = lean_ctor_get(x_3, 4);
lean_inc(x_106);
x_107 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_108 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_109 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_110 = lean_ctor_get(x_3, 5);
lean_inc(x_110);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_111 = x_3;
} else {
 lean_dec_ref(x_3);
 x_111 = lean_box(0);
}
lean_inc(x_101);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_1);
lean_ctor_set(x_112, 1, x_101);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_105);
if (lean_is_scalar(x_111)) {
 x_114 = lean_alloc_ctor(0, 6, 3);
} else {
 x_114 = x_111;
}
lean_ctor_set(x_114, 0, x_102);
lean_ctor_set(x_114, 1, x_103);
lean_ctor_set(x_114, 2, x_104);
lean_ctor_set(x_114, 3, x_113);
lean_ctor_set(x_114, 4, x_106);
lean_ctor_set(x_114, 5, x_110);
lean_ctor_set_uint8(x_114, sizeof(void*)*6, x_107);
lean_ctor_set_uint8(x_114, sizeof(void*)*6 + 1, x_108);
lean_ctor_set_uint8(x_114, sizeof(void*)*6 + 2, x_109);
x_115 = 1;
x_116 = l_Lean_Elab_Term_elabTerm(x_101, x_2, x_115, x_114, x_4, x_5, x_6, x_7, x_8, x_91);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_47);
lean_dec(x_40);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_117 = l_Lean_indentExpr(x_23);
x_118 = l_Lean_Elab_Term_elabAnonymousCtor___closed__7;
x_119 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
x_120 = l_Lean_KernelException_toMessageData___closed__15;
x_121 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_121, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_38);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_123 = l_Lean_indentExpr(x_23);
x_124 = l_Lean_Elab_Term_elabAnonymousCtor___closed__5;
x_125 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = l_Lean_KernelException_toMessageData___closed__15;
x_127 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_127, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_129 = l_Lean_indentExpr(x_23);
x_130 = l_Lean_Elab_Term_elabAnonymousCtor___closed__5;
x_131 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = l_Lean_KernelException_toMessageData___closed__15;
x_133 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_133, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_134;
}
}
else
{
uint8_t x_135; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_22);
if (x_135 == 0)
{
return x_22;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_22, 0);
x_137 = lean_ctor_get(x_22, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_22);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_16);
if (x_139 == 0)
{
return x_16;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_16, 0);
x_141 = lean_ctor_get(x_16, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_16);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabAnonymousCtor), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabBorrowed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Parser_Term_borrowed___elambda__1___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = 1;
x_16 = l_Lean_Elab_Term_elabTerm(x_14, x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_Lean_markBorrowed(x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = l_Lean_markBorrowed(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabBorrowed___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBorrowed), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabBorrowed(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_borrowed___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabBorrowed___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("from");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("by");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("this");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandShow___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandShow(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Term_show___elambda__1___closed__1;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Parser_Term_fromTerm___elambda__1___closed__2;
lean_inc(x_11);
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_1);
x_14 = l_Lean_Parser_Term_byTactic___elambda__1___closed__2;
lean_inc(x_11);
x_15 = l_Lean_Syntax_isOfKind(x_11, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_9);
x_16 = lean_box(1);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Syntax_getArg(x_11, x_8);
lean_dec(x_11);
x_19 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_14558____closed__3;
lean_inc(x_18);
x_20 = l_Lean_Syntax_isOfKind(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_9);
x_21 = lean_box(1);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_Lean_Parser_Tactic_show___closed__1;
lean_inc(x_25);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Array_empty___closed__1;
x_29 = lean_array_push(x_28, x_27);
x_30 = lean_array_push(x_29, x_9);
x_31 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_25);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_array_push(x_28, x_32);
x_34 = l_Lean_Elab_Term_expandShow___closed__2;
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_array_push(x_28, x_35);
x_37 = lean_array_push(x_36, x_18);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_14);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_array_push(x_33, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_12);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_array_push(x_30, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_23, 0, x_42);
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
x_45 = l_Lean_Parser_Tactic_show___closed__1;
lean_inc(x_43);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Array_empty___closed__1;
x_48 = lean_array_push(x_47, x_46);
x_49 = lean_array_push(x_48, x_9);
x_50 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_43);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_array_push(x_47, x_51);
x_53 = l_Lean_Elab_Term_expandShow___closed__2;
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_array_push(x_47, x_54);
x_56 = lean_array_push(x_55, x_18);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_14);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_array_push(x_52, x_57);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_12);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_array_push(x_49, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_4);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_44);
return x_62;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = l_Lean_Syntax_getArg(x_11, x_8);
lean_dec(x_11);
x_64 = l_Lean_Elab_Term_expandShow___closed__4;
x_65 = l_Lean_mkIdentFrom(x_1, x_64);
lean_dec(x_1);
x_66 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = l_Lean_Parser_Tactic_let_x21___closed__1;
lean_inc(x_68);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Array_empty___closed__1;
x_72 = lean_array_push(x_71, x_70);
lean_inc(x_65);
x_73 = lean_array_push(x_71, x_65);
x_74 = l_myMacro____x40_Init_Notation___hyg_1192____closed__8;
x_75 = lean_array_push(x_73, x_74);
x_76 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_68);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_array_push(x_71, x_77);
x_79 = lean_array_push(x_78, x_9);
x_80 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_array_push(x_71, x_81);
x_83 = l_Lean_nullKind___closed__2;
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = lean_array_push(x_75, x_84);
x_86 = l_myMacro____x40_Init_Notation___hyg_13394____closed__11;
lean_inc(x_68);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_68);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_array_push(x_85, x_87);
x_89 = lean_array_push(x_88, x_63);
x_90 = l_myMacro____x40_Init_Notation___hyg_13394____closed__6;
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_array_push(x_71, x_91);
x_93 = l_myMacro____x40_Init_Notation___hyg_13394____closed__4;
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = lean_array_push(x_72, x_94);
x_96 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_68);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_array_push(x_71, x_97);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_83);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_array_push(x_95, x_99);
x_101 = lean_array_push(x_100, x_65);
x_102 = l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
lean_ctor_set(x_66, 0, x_103);
return x_66;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_104 = lean_ctor_get(x_66, 0);
x_105 = lean_ctor_get(x_66, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_66);
x_106 = l_Lean_Parser_Tactic_let_x21___closed__1;
lean_inc(x_104);
x_107 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Array_empty___closed__1;
x_109 = lean_array_push(x_108, x_107);
lean_inc(x_65);
x_110 = lean_array_push(x_108, x_65);
x_111 = l_myMacro____x40_Init_Notation___hyg_1192____closed__8;
x_112 = lean_array_push(x_110, x_111);
x_113 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_104);
x_114 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_114, 0, x_104);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_array_push(x_108, x_114);
x_116 = lean_array_push(x_115, x_9);
x_117 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_array_push(x_108, x_118);
x_120 = l_Lean_nullKind___closed__2;
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = lean_array_push(x_112, x_121);
x_123 = l_myMacro____x40_Init_Notation___hyg_13394____closed__11;
lean_inc(x_104);
x_124 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_124, 0, x_104);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_array_push(x_122, x_124);
x_126 = lean_array_push(x_125, x_63);
x_127 = l_myMacro____x40_Init_Notation___hyg_13394____closed__6;
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
x_129 = lean_array_push(x_108, x_128);
x_130 = l_myMacro____x40_Init_Notation___hyg_13394____closed__4;
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = lean_array_push(x_109, x_131);
x_133 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_134 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_134, 0, x_104);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_array_push(x_108, x_134);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_120);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_array_push(x_132, x_136);
x_138 = lean_array_push(x_137, x_65);
x_139 = l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_105);
return x_141;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_expandShow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandShow(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandShow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandShow___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandShow(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_Lean_Parser_Term_show___elambda__1___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandShow___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandHave_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_expandHave_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandHave_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandHave_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_expandHave_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandHave_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandHave_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_expandHave_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandHave_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandHave_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_expandHave_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandHave_match__4___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandHave___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Array_appendCore___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandHave___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l_Lean_Elab_Term_expandHave___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandHave(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Term_have___elambda__1___closed__1;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_isNone(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_nullKind___closed__2;
lean_inc(x_9);
x_12 = l_Lean_Syntax_isOfKind(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_1);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = l_Lean_Syntax_getArgs(x_9);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_1);
x_19 = lean_box(1);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_9, x_21);
lean_dec(x_9);
x_23 = l_Lean_Syntax_getArg(x_1, x_17);
x_24 = lean_unsigned_to_nat(3u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
x_26 = l_Lean_Parser_Term_fromTerm___elambda__1___closed__2;
lean_inc(x_25);
x_27 = l_Lean_Syntax_isOfKind(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_16359____closed__2;
lean_inc(x_25);
x_29 = l_Lean_Syntax_isOfKind(x_25, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Parser_Term_byTactic___elambda__1___closed__2;
lean_inc(x_25);
x_31 = l_Lean_Syntax_isOfKind(x_25, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_32 = lean_box(1);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_3);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = l_Lean_Syntax_getArg(x_25, x_8);
lean_dec(x_25);
x_35 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_14558____closed__3;
lean_inc(x_34);
x_36 = l_Lean_Syntax_isOfKind(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_37 = lean_box(1);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_3);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_unsigned_to_nat(4u);
x_40 = l_Lean_Syntax_getArg(x_1, x_39);
x_41 = l_Lean_Syntax_isNone(x_40);
if (x_41 == 0)
{
uint8_t x_42; 
lean_inc(x_40);
x_42 = l_Lean_Syntax_isOfKind(x_40, x_11);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_40);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_43 = lean_box(1);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_3);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = l_Lean_Syntax_getArgs(x_40);
lean_dec(x_40);
x_46 = lean_array_get_size(x_45);
lean_dec(x_45);
x_47 = lean_nat_dec_eq(x_46, x_8);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_48 = lean_box(1);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_3);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_unsigned_to_nat(5u);
x_51 = l_Lean_Syntax_getArg(x_1, x_50);
lean_dec(x_1);
x_52 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_54);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Array_empty___closed__1;
x_58 = lean_array_push(x_57, x_56);
x_59 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_54);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Syntax_mkApp___closed__1;
x_62 = lean_array_push(x_61, x_22);
x_63 = lean_array_push(x_62, x_60);
x_64 = l_Array_appendCore___rarg(x_57, x_63);
lean_dec(x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_11);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_array_push(x_58, x_65);
x_67 = lean_array_push(x_66, x_23);
x_68 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_54);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_54);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_array_push(x_57, x_69);
x_71 = l_Lean_Elab_Term_expandShow___closed__2;
lean_inc(x_54);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_54);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_array_push(x_57, x_72);
x_74 = lean_array_push(x_73, x_34);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_30);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_array_push(x_70, x_75);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_26);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_array_push(x_67, x_77);
x_79 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_54);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_array_push(x_57, x_80);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_11);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_array_push(x_78, x_82);
x_84 = lean_array_push(x_83, x_51);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_4);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_52, 0, x_85);
return x_52;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_86 = lean_ctor_get(x_52, 0);
x_87 = lean_ctor_get(x_52, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_52);
x_88 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_86);
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Array_empty___closed__1;
x_91 = lean_array_push(x_90, x_89);
x_92 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_86);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_86);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_Syntax_mkApp___closed__1;
x_95 = lean_array_push(x_94, x_22);
x_96 = lean_array_push(x_95, x_93);
x_97 = l_Array_appendCore___rarg(x_90, x_96);
lean_dec(x_96);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_11);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_array_push(x_91, x_98);
x_100 = lean_array_push(x_99, x_23);
x_101 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_86);
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_86);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_array_push(x_90, x_102);
x_104 = l_Lean_Elab_Term_expandShow___closed__2;
lean_inc(x_86);
x_105 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_105, 0, x_86);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_array_push(x_90, x_105);
x_107 = lean_array_push(x_106, x_34);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_30);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_array_push(x_103, x_108);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_26);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_array_push(x_100, x_110);
x_112 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_113 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_113, 0, x_86);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_array_push(x_90, x_113);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_11);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_array_push(x_111, x_115);
x_117 = lean_array_push(x_116, x_51);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_4);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_87);
return x_119;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
lean_dec(x_40);
x_120 = lean_unsigned_to_nat(5u);
x_121 = l_Lean_Syntax_getArg(x_1, x_120);
lean_dec(x_1);
x_122 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_124 = lean_ctor_get(x_122, 0);
x_125 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_124);
x_126 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Array_empty___closed__1;
x_128 = lean_array_push(x_127, x_126);
x_129 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_124);
x_130 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_130, 0, x_124);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_Syntax_mkApp___closed__1;
x_132 = lean_array_push(x_131, x_22);
x_133 = lean_array_push(x_132, x_130);
x_134 = l_Array_appendCore___rarg(x_127, x_133);
lean_dec(x_133);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_11);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_array_push(x_128, x_135);
x_137 = lean_array_push(x_136, x_23);
x_138 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_124);
x_139 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_139, 0, x_124);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_array_push(x_127, x_139);
x_141 = l_Lean_Elab_Term_expandShow___closed__2;
lean_inc(x_124);
x_142 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_142, 0, x_124);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_array_push(x_127, x_142);
x_144 = lean_array_push(x_143, x_34);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_30);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_array_push(x_140, x_145);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_26);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_array_push(x_137, x_147);
x_149 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_150 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_150, 0, x_124);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_array_push(x_127, x_150);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_11);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_array_push(x_148, x_152);
x_154 = lean_array_push(x_153, x_121);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_4);
lean_ctor_set(x_155, 1, x_154);
lean_ctor_set(x_122, 0, x_155);
return x_122;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_156 = lean_ctor_get(x_122, 0);
x_157 = lean_ctor_get(x_122, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_122);
x_158 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_156);
x_159 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Array_empty___closed__1;
x_161 = lean_array_push(x_160, x_159);
x_162 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_156);
x_163 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_163, 0, x_156);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Lean_Syntax_mkApp___closed__1;
x_165 = lean_array_push(x_164, x_22);
x_166 = lean_array_push(x_165, x_163);
x_167 = l_Array_appendCore___rarg(x_160, x_166);
lean_dec(x_166);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_11);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_array_push(x_161, x_168);
x_170 = lean_array_push(x_169, x_23);
x_171 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_156);
x_172 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_172, 0, x_156);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_array_push(x_160, x_172);
x_174 = l_Lean_Elab_Term_expandShow___closed__2;
lean_inc(x_156);
x_175 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_175, 0, x_156);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_array_push(x_160, x_175);
x_177 = lean_array_push(x_176, x_34);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_30);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_array_push(x_173, x_178);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_26);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_array_push(x_170, x_180);
x_182 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_183 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_183, 0, x_156);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_array_push(x_160, x_183);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_11);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_array_push(x_181, x_185);
x_187 = lean_array_push(x_186, x_121);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_4);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_157);
return x_189;
}
}
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_190 = l_Lean_Syntax_getArg(x_25, x_8);
lean_dec(x_25);
x_191 = lean_unsigned_to_nat(4u);
x_192 = l_Lean_Syntax_getArg(x_1, x_191);
x_193 = l_Lean_Syntax_isNone(x_192);
if (x_193 == 0)
{
uint8_t x_194; 
lean_inc(x_192);
x_194 = l_Lean_Syntax_isOfKind(x_192, x_11);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_192);
lean_dec(x_190);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_195 = lean_box(1);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_3);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_197 = l_Lean_Syntax_getArgs(x_192);
lean_dec(x_192);
x_198 = lean_array_get_size(x_197);
lean_dec(x_197);
x_199 = lean_nat_dec_eq(x_198, x_8);
lean_dec(x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_190);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_200 = lean_box(1);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_3);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_202 = lean_unsigned_to_nat(5u);
x_203 = l_Lean_Syntax_getArg(x_1, x_202);
lean_dec(x_1);
x_204 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_205 = !lean_is_exclusive(x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_206 = lean_ctor_get(x_204, 0);
x_207 = l_Lean_Parser_Tactic_let_x21___closed__1;
lean_inc(x_206);
x_208 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = l_Array_empty___closed__1;
x_210 = lean_array_push(x_209, x_208);
x_211 = lean_array_push(x_209, x_22);
x_212 = l_myMacro____x40_Init_Notation___hyg_12817____closed__10;
x_213 = lean_array_push(x_211, x_212);
x_214 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_206);
x_215 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_215, 0, x_206);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_array_push(x_209, x_215);
x_217 = lean_array_push(x_216, x_23);
x_218 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_217);
x_220 = lean_array_push(x_209, x_219);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_11);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_array_push(x_213, x_221);
x_223 = l_myMacro____x40_Init_Notation___hyg_13394____closed__11;
lean_inc(x_206);
x_224 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_224, 0, x_206);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_array_push(x_222, x_224);
x_226 = lean_array_push(x_225, x_190);
x_227 = l_myMacro____x40_Init_Notation___hyg_13394____closed__6;
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_226);
x_229 = lean_array_push(x_209, x_228);
x_230 = l_myMacro____x40_Init_Notation___hyg_13394____closed__4;
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_229);
x_232 = lean_array_push(x_210, x_231);
x_233 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_234 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_234, 0, x_206);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_array_push(x_209, x_234);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_11);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_array_push(x_232, x_236);
x_238 = lean_array_push(x_237, x_203);
x_239 = l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_238);
lean_ctor_set(x_204, 0, x_240);
return x_204;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_241 = lean_ctor_get(x_204, 0);
x_242 = lean_ctor_get(x_204, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_204);
x_243 = l_Lean_Parser_Tactic_let_x21___closed__1;
lean_inc(x_241);
x_244 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_243);
x_245 = l_Array_empty___closed__1;
x_246 = lean_array_push(x_245, x_244);
x_247 = lean_array_push(x_245, x_22);
x_248 = l_myMacro____x40_Init_Notation___hyg_12817____closed__10;
x_249 = lean_array_push(x_247, x_248);
x_250 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_241);
x_251 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_251, 0, x_241);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_array_push(x_245, x_251);
x_253 = lean_array_push(x_252, x_23);
x_254 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_253);
x_256 = lean_array_push(x_245, x_255);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_11);
lean_ctor_set(x_257, 1, x_256);
x_258 = lean_array_push(x_249, x_257);
x_259 = l_myMacro____x40_Init_Notation___hyg_13394____closed__11;
lean_inc(x_241);
x_260 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_260, 0, x_241);
lean_ctor_set(x_260, 1, x_259);
x_261 = lean_array_push(x_258, x_260);
x_262 = lean_array_push(x_261, x_190);
x_263 = l_myMacro____x40_Init_Notation___hyg_13394____closed__6;
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_262);
x_265 = lean_array_push(x_245, x_264);
x_266 = l_myMacro____x40_Init_Notation___hyg_13394____closed__4;
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_265);
x_268 = lean_array_push(x_246, x_267);
x_269 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_270 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_270, 0, x_241);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_array_push(x_245, x_270);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_11);
lean_ctor_set(x_272, 1, x_271);
x_273 = lean_array_push(x_268, x_272);
x_274 = lean_array_push(x_273, x_203);
x_275 = l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_274);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_242);
return x_277;
}
}
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
lean_dec(x_192);
x_278 = lean_unsigned_to_nat(5u);
x_279 = l_Lean_Syntax_getArg(x_1, x_278);
lean_dec(x_1);
x_280 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_281 = !lean_is_exclusive(x_280);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_282 = lean_ctor_get(x_280, 0);
x_283 = l_Lean_Parser_Tactic_let_x21___closed__1;
lean_inc(x_282);
x_284 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
x_285 = l_Array_empty___closed__1;
x_286 = lean_array_push(x_285, x_284);
x_287 = lean_array_push(x_285, x_22);
x_288 = l_myMacro____x40_Init_Notation___hyg_12817____closed__10;
x_289 = lean_array_push(x_287, x_288);
x_290 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_282);
x_291 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_291, 0, x_282);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_array_push(x_285, x_291);
x_293 = lean_array_push(x_292, x_23);
x_294 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_293);
x_296 = lean_array_push(x_285, x_295);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_11);
lean_ctor_set(x_297, 1, x_296);
x_298 = lean_array_push(x_289, x_297);
x_299 = l_myMacro____x40_Init_Notation___hyg_13394____closed__11;
lean_inc(x_282);
x_300 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_300, 0, x_282);
lean_ctor_set(x_300, 1, x_299);
x_301 = lean_array_push(x_298, x_300);
x_302 = lean_array_push(x_301, x_190);
x_303 = l_myMacro____x40_Init_Notation___hyg_13394____closed__6;
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_302);
x_305 = lean_array_push(x_285, x_304);
x_306 = l_myMacro____x40_Init_Notation___hyg_13394____closed__4;
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_305);
x_308 = lean_array_push(x_286, x_307);
x_309 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_310 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_310, 0, x_282);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_array_push(x_285, x_310);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_11);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_array_push(x_308, x_312);
x_314 = lean_array_push(x_313, x_279);
x_315 = l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_314);
lean_ctor_set(x_280, 0, x_316);
return x_280;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_317 = lean_ctor_get(x_280, 0);
x_318 = lean_ctor_get(x_280, 1);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_280);
x_319 = l_Lean_Parser_Tactic_let_x21___closed__1;
lean_inc(x_317);
x_320 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_319);
x_321 = l_Array_empty___closed__1;
x_322 = lean_array_push(x_321, x_320);
x_323 = lean_array_push(x_321, x_22);
x_324 = l_myMacro____x40_Init_Notation___hyg_12817____closed__10;
x_325 = lean_array_push(x_323, x_324);
x_326 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_317);
x_327 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_327, 0, x_317);
lean_ctor_set(x_327, 1, x_326);
x_328 = lean_array_push(x_321, x_327);
x_329 = lean_array_push(x_328, x_23);
x_330 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_329);
x_332 = lean_array_push(x_321, x_331);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_11);
lean_ctor_set(x_333, 1, x_332);
x_334 = lean_array_push(x_325, x_333);
x_335 = l_myMacro____x40_Init_Notation___hyg_13394____closed__11;
lean_inc(x_317);
x_336 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_336, 0, x_317);
lean_ctor_set(x_336, 1, x_335);
x_337 = lean_array_push(x_334, x_336);
x_338 = lean_array_push(x_337, x_190);
x_339 = l_myMacro____x40_Init_Notation___hyg_13394____closed__6;
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_338);
x_341 = lean_array_push(x_321, x_340);
x_342 = l_myMacro____x40_Init_Notation___hyg_13394____closed__4;
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_341);
x_344 = lean_array_push(x_322, x_343);
x_345 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_346 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_346, 0, x_317);
lean_ctor_set(x_346, 1, x_345);
x_347 = lean_array_push(x_321, x_346);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_11);
lean_ctor_set(x_348, 1, x_347);
x_349 = lean_array_push(x_344, x_348);
x_350 = lean_array_push(x_349, x_279);
x_351 = l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_350);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_318);
return x_353;
}
}
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_354 = l_Lean_Syntax_getArg(x_25, x_8);
lean_dec(x_25);
x_355 = lean_unsigned_to_nat(4u);
x_356 = l_Lean_Syntax_getArg(x_1, x_355);
x_357 = l_Lean_Syntax_isNone(x_356);
if (x_357 == 0)
{
uint8_t x_358; 
lean_inc(x_356);
x_358 = l_Lean_Syntax_isOfKind(x_356, x_11);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; 
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_359 = lean_box(1);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_3);
return x_360;
}
else
{
lean_object* x_361; lean_object* x_362; uint8_t x_363; 
x_361 = l_Lean_Syntax_getArgs(x_356);
lean_dec(x_356);
x_362 = lean_array_get_size(x_361);
lean_dec(x_361);
x_363 = lean_nat_dec_eq(x_362, x_8);
lean_dec(x_362);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; 
lean_dec(x_354);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_364 = lean_box(1);
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_3);
return x_365;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_366 = lean_unsigned_to_nat(5u);
x_367 = l_Lean_Syntax_getArg(x_1, x_366);
lean_dec(x_1);
x_368 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_369 = !lean_is_exclusive(x_368);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_370 = lean_ctor_get(x_368, 0);
x_371 = l_Lean_Parser_Tactic_let_x21___closed__1;
lean_inc(x_370);
x_372 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
x_373 = l_Array_empty___closed__1;
x_374 = lean_array_push(x_373, x_372);
x_375 = lean_array_push(x_373, x_22);
x_376 = l_myMacro____x40_Init_Notation___hyg_12817____closed__10;
x_377 = lean_array_push(x_375, x_376);
x_378 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_370);
x_379 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_379, 0, x_370);
lean_ctor_set(x_379, 1, x_378);
x_380 = lean_array_push(x_373, x_379);
x_381 = lean_array_push(x_380, x_23);
x_382 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_381);
x_384 = lean_array_push(x_373, x_383);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_11);
lean_ctor_set(x_385, 1, x_384);
x_386 = lean_array_push(x_377, x_385);
x_387 = l_myMacro____x40_Init_Notation___hyg_13394____closed__11;
lean_inc(x_370);
x_388 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_388, 0, x_370);
lean_ctor_set(x_388, 1, x_387);
x_389 = lean_array_push(x_386, x_388);
x_390 = lean_array_push(x_389, x_354);
x_391 = l_myMacro____x40_Init_Notation___hyg_13394____closed__6;
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_390);
x_393 = lean_array_push(x_373, x_392);
x_394 = l_myMacro____x40_Init_Notation___hyg_13394____closed__4;
x_395 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_393);
x_396 = lean_array_push(x_374, x_395);
x_397 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_398 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_398, 0, x_370);
lean_ctor_set(x_398, 1, x_397);
x_399 = lean_array_push(x_373, x_398);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_11);
lean_ctor_set(x_400, 1, x_399);
x_401 = lean_array_push(x_396, x_400);
x_402 = lean_array_push(x_401, x_367);
x_403 = l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_402);
lean_ctor_set(x_368, 0, x_404);
return x_368;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_405 = lean_ctor_get(x_368, 0);
x_406 = lean_ctor_get(x_368, 1);
lean_inc(x_406);
lean_inc(x_405);
lean_dec(x_368);
x_407 = l_Lean_Parser_Tactic_let_x21___closed__1;
lean_inc(x_405);
x_408 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_408, 0, x_405);
lean_ctor_set(x_408, 1, x_407);
x_409 = l_Array_empty___closed__1;
x_410 = lean_array_push(x_409, x_408);
x_411 = lean_array_push(x_409, x_22);
x_412 = l_myMacro____x40_Init_Notation___hyg_12817____closed__10;
x_413 = lean_array_push(x_411, x_412);
x_414 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_405);
x_415 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_415, 0, x_405);
lean_ctor_set(x_415, 1, x_414);
x_416 = lean_array_push(x_409, x_415);
x_417 = lean_array_push(x_416, x_23);
x_418 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_419 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_417);
x_420 = lean_array_push(x_409, x_419);
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_11);
lean_ctor_set(x_421, 1, x_420);
x_422 = lean_array_push(x_413, x_421);
x_423 = l_myMacro____x40_Init_Notation___hyg_13394____closed__11;
lean_inc(x_405);
x_424 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_424, 0, x_405);
lean_ctor_set(x_424, 1, x_423);
x_425 = lean_array_push(x_422, x_424);
x_426 = lean_array_push(x_425, x_354);
x_427 = l_myMacro____x40_Init_Notation___hyg_13394____closed__6;
x_428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_426);
x_429 = lean_array_push(x_409, x_428);
x_430 = l_myMacro____x40_Init_Notation___hyg_13394____closed__4;
x_431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_429);
x_432 = lean_array_push(x_410, x_431);
x_433 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_434 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_434, 0, x_405);
lean_ctor_set(x_434, 1, x_433);
x_435 = lean_array_push(x_409, x_434);
x_436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_436, 0, x_11);
lean_ctor_set(x_436, 1, x_435);
x_437 = lean_array_push(x_432, x_436);
x_438 = lean_array_push(x_437, x_367);
x_439 = l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
x_440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_438);
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_406);
return x_441;
}
}
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; 
lean_dec(x_356);
x_442 = lean_unsigned_to_nat(5u);
x_443 = l_Lean_Syntax_getArg(x_1, x_442);
lean_dec(x_1);
x_444 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_445 = !lean_is_exclusive(x_444);
if (x_445 == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_446 = lean_ctor_get(x_444, 0);
x_447 = l_Lean_Parser_Tactic_let_x21___closed__1;
lean_inc(x_446);
x_448 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_448, 0, x_446);
lean_ctor_set(x_448, 1, x_447);
x_449 = l_Array_empty___closed__1;
x_450 = lean_array_push(x_449, x_448);
x_451 = lean_array_push(x_449, x_22);
x_452 = l_myMacro____x40_Init_Notation___hyg_12817____closed__10;
x_453 = lean_array_push(x_451, x_452);
x_454 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_446);
x_455 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_455, 0, x_446);
lean_ctor_set(x_455, 1, x_454);
x_456 = lean_array_push(x_449, x_455);
x_457 = lean_array_push(x_456, x_23);
x_458 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_459 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_457);
x_460 = lean_array_push(x_449, x_459);
x_461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_461, 0, x_11);
lean_ctor_set(x_461, 1, x_460);
x_462 = lean_array_push(x_453, x_461);
x_463 = l_myMacro____x40_Init_Notation___hyg_13394____closed__11;
lean_inc(x_446);
x_464 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_464, 0, x_446);
lean_ctor_set(x_464, 1, x_463);
x_465 = lean_array_push(x_462, x_464);
x_466 = lean_array_push(x_465, x_354);
x_467 = l_myMacro____x40_Init_Notation___hyg_13394____closed__6;
x_468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_466);
x_469 = lean_array_push(x_449, x_468);
x_470 = l_myMacro____x40_Init_Notation___hyg_13394____closed__4;
x_471 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_471, 0, x_470);
lean_ctor_set(x_471, 1, x_469);
x_472 = lean_array_push(x_450, x_471);
x_473 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_474 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_474, 0, x_446);
lean_ctor_set(x_474, 1, x_473);
x_475 = lean_array_push(x_449, x_474);
x_476 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_476, 0, x_11);
lean_ctor_set(x_476, 1, x_475);
x_477 = lean_array_push(x_472, x_476);
x_478 = lean_array_push(x_477, x_443);
x_479 = l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
x_480 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_480, 0, x_479);
lean_ctor_set(x_480, 1, x_478);
lean_ctor_set(x_444, 0, x_480);
return x_444;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_481 = lean_ctor_get(x_444, 0);
x_482 = lean_ctor_get(x_444, 1);
lean_inc(x_482);
lean_inc(x_481);
lean_dec(x_444);
x_483 = l_Lean_Parser_Tactic_let_x21___closed__1;
lean_inc(x_481);
x_484 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_484, 0, x_481);
lean_ctor_set(x_484, 1, x_483);
x_485 = l_Array_empty___closed__1;
x_486 = lean_array_push(x_485, x_484);
x_487 = lean_array_push(x_485, x_22);
x_488 = l_myMacro____x40_Init_Notation___hyg_12817____closed__10;
x_489 = lean_array_push(x_487, x_488);
x_490 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_481);
x_491 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_491, 0, x_481);
lean_ctor_set(x_491, 1, x_490);
x_492 = lean_array_push(x_485, x_491);
x_493 = lean_array_push(x_492, x_23);
x_494 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_495 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_495, 0, x_494);
lean_ctor_set(x_495, 1, x_493);
x_496 = lean_array_push(x_485, x_495);
x_497 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_497, 0, x_11);
lean_ctor_set(x_497, 1, x_496);
x_498 = lean_array_push(x_489, x_497);
x_499 = l_myMacro____x40_Init_Notation___hyg_13394____closed__11;
lean_inc(x_481);
x_500 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_500, 0, x_481);
lean_ctor_set(x_500, 1, x_499);
x_501 = lean_array_push(x_498, x_500);
x_502 = lean_array_push(x_501, x_354);
x_503 = l_myMacro____x40_Init_Notation___hyg_13394____closed__6;
x_504 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_504, 0, x_503);
lean_ctor_set(x_504, 1, x_502);
x_505 = lean_array_push(x_485, x_504);
x_506 = l_myMacro____x40_Init_Notation___hyg_13394____closed__4;
x_507 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_507, 0, x_506);
lean_ctor_set(x_507, 1, x_505);
x_508 = lean_array_push(x_486, x_507);
x_509 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_510 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_510, 0, x_481);
lean_ctor_set(x_510, 1, x_509);
x_511 = lean_array_push(x_485, x_510);
x_512 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_512, 0, x_11);
lean_ctor_set(x_512, 1, x_511);
x_513 = lean_array_push(x_508, x_512);
x_514 = lean_array_push(x_513, x_443);
x_515 = l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
x_516 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_516, 0, x_515);
lean_ctor_set(x_516, 1, x_514);
x_517 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_517, 0, x_516);
lean_ctor_set(x_517, 1, x_482);
return x_517;
}
}
}
}
}
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; uint8_t x_523; 
lean_dec(x_9);
x_518 = lean_unsigned_to_nat(2u);
x_519 = l_Lean_Syntax_getArg(x_1, x_518);
x_520 = lean_unsigned_to_nat(3u);
x_521 = l_Lean_Syntax_getArg(x_1, x_520);
x_522 = l_Lean_Parser_Term_fromTerm___elambda__1___closed__2;
lean_inc(x_521);
x_523 = l_Lean_Syntax_isOfKind(x_521, x_522);
if (x_523 == 0)
{
lean_object* x_524; uint8_t x_525; 
x_524 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_16359____closed__2;
lean_inc(x_521);
x_525 = l_Lean_Syntax_isOfKind(x_521, x_524);
if (x_525 == 0)
{
lean_object* x_526; uint8_t x_527; 
x_526 = l_Lean_Parser_Term_byTactic___elambda__1___closed__2;
lean_inc(x_521);
x_527 = l_Lean_Syntax_isOfKind(x_521, x_526);
if (x_527 == 0)
{
lean_object* x_528; lean_object* x_529; 
lean_dec(x_521);
lean_dec(x_519);
lean_dec(x_1);
x_528 = lean_box(1);
x_529 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_529, 0, x_528);
lean_ctor_set(x_529, 1, x_3);
return x_529;
}
else
{
lean_object* x_530; lean_object* x_531; uint8_t x_532; 
x_530 = l_Lean_Syntax_getArg(x_521, x_8);
lean_dec(x_521);
x_531 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_14558____closed__3;
lean_inc(x_530);
x_532 = l_Lean_Syntax_isOfKind(x_530, x_531);
if (x_532 == 0)
{
lean_object* x_533; lean_object* x_534; 
lean_dec(x_530);
lean_dec(x_519);
lean_dec(x_1);
x_533 = lean_box(1);
x_534 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_534, 0, x_533);
lean_ctor_set(x_534, 1, x_3);
return x_534;
}
else
{
lean_object* x_535; lean_object* x_536; uint8_t x_537; 
x_535 = lean_unsigned_to_nat(4u);
x_536 = l_Lean_Syntax_getArg(x_1, x_535);
x_537 = l_Lean_Syntax_isNone(x_536);
if (x_537 == 0)
{
lean_object* x_538; uint8_t x_539; 
x_538 = l_Lean_nullKind___closed__2;
lean_inc(x_536);
x_539 = l_Lean_Syntax_isOfKind(x_536, x_538);
if (x_539 == 0)
{
lean_object* x_540; lean_object* x_541; 
lean_dec(x_536);
lean_dec(x_530);
lean_dec(x_519);
lean_dec(x_1);
x_540 = lean_box(1);
x_541 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_541, 0, x_540);
lean_ctor_set(x_541, 1, x_3);
return x_541;
}
else
{
lean_object* x_542; lean_object* x_543; uint8_t x_544; 
x_542 = l_Lean_Syntax_getArgs(x_536);
lean_dec(x_536);
x_543 = lean_array_get_size(x_542);
lean_dec(x_542);
x_544 = lean_nat_dec_eq(x_543, x_8);
lean_dec(x_543);
if (x_544 == 0)
{
lean_object* x_545; lean_object* x_546; 
lean_dec(x_530);
lean_dec(x_519);
lean_dec(x_1);
x_545 = lean_box(1);
x_546 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_546, 0, x_545);
lean_ctor_set(x_546, 1, x_3);
return x_546;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; uint8_t x_550; 
x_547 = lean_unsigned_to_nat(5u);
x_548 = l_Lean_Syntax_getArg(x_1, x_547);
lean_dec(x_1);
x_549 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_550 = !lean_is_exclusive(x_549);
if (x_550 == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_551 = lean_ctor_get(x_549, 0);
x_552 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_551);
x_553 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_553, 0, x_551);
lean_ctor_set(x_553, 1, x_552);
x_554 = l_Array_empty___closed__1;
x_555 = lean_array_push(x_554, x_553);
x_556 = l_Lean_Elab_Term_expandHave___closed__2;
x_557 = lean_array_push(x_555, x_556);
x_558 = lean_array_push(x_557, x_519);
x_559 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_551);
x_560 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_560, 0, x_551);
lean_ctor_set(x_560, 1, x_559);
x_561 = lean_array_push(x_554, x_560);
x_562 = l_Lean_Elab_Term_expandShow___closed__2;
lean_inc(x_551);
x_563 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_563, 0, x_551);
lean_ctor_set(x_563, 1, x_562);
x_564 = lean_array_push(x_554, x_563);
x_565 = lean_array_push(x_564, x_530);
x_566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_566, 0, x_526);
lean_ctor_set(x_566, 1, x_565);
x_567 = lean_array_push(x_561, x_566);
x_568 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_568, 0, x_522);
lean_ctor_set(x_568, 1, x_567);
x_569 = lean_array_push(x_558, x_568);
x_570 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_571 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_571, 0, x_551);
lean_ctor_set(x_571, 1, x_570);
x_572 = lean_array_push(x_554, x_571);
x_573 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_573, 0, x_538);
lean_ctor_set(x_573, 1, x_572);
x_574 = lean_array_push(x_569, x_573);
x_575 = lean_array_push(x_574, x_548);
x_576 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_576, 0, x_4);
lean_ctor_set(x_576, 1, x_575);
lean_ctor_set(x_549, 0, x_576);
return x_549;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_577 = lean_ctor_get(x_549, 0);
x_578 = lean_ctor_get(x_549, 1);
lean_inc(x_578);
lean_inc(x_577);
lean_dec(x_549);
x_579 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_577);
x_580 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_580, 0, x_577);
lean_ctor_set(x_580, 1, x_579);
x_581 = l_Array_empty___closed__1;
x_582 = lean_array_push(x_581, x_580);
x_583 = l_Lean_Elab_Term_expandHave___closed__2;
x_584 = lean_array_push(x_582, x_583);
x_585 = lean_array_push(x_584, x_519);
x_586 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_577);
x_587 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_587, 0, x_577);
lean_ctor_set(x_587, 1, x_586);
x_588 = lean_array_push(x_581, x_587);
x_589 = l_Lean_Elab_Term_expandShow___closed__2;
lean_inc(x_577);
x_590 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_590, 0, x_577);
lean_ctor_set(x_590, 1, x_589);
x_591 = lean_array_push(x_581, x_590);
x_592 = lean_array_push(x_591, x_530);
x_593 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_593, 0, x_526);
lean_ctor_set(x_593, 1, x_592);
x_594 = lean_array_push(x_588, x_593);
x_595 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_595, 0, x_522);
lean_ctor_set(x_595, 1, x_594);
x_596 = lean_array_push(x_585, x_595);
x_597 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_598 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_598, 0, x_577);
lean_ctor_set(x_598, 1, x_597);
x_599 = lean_array_push(x_581, x_598);
x_600 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_600, 0, x_538);
lean_ctor_set(x_600, 1, x_599);
x_601 = lean_array_push(x_596, x_600);
x_602 = lean_array_push(x_601, x_548);
x_603 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_603, 0, x_4);
lean_ctor_set(x_603, 1, x_602);
x_604 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_604, 0, x_603);
lean_ctor_set(x_604, 1, x_578);
return x_604;
}
}
}
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; uint8_t x_608; 
lean_dec(x_536);
x_605 = lean_unsigned_to_nat(5u);
x_606 = l_Lean_Syntax_getArg(x_1, x_605);
lean_dec(x_1);
x_607 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_608 = !lean_is_exclusive(x_607);
if (x_608 == 0)
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_609 = lean_ctor_get(x_607, 0);
x_610 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_609);
x_611 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_611, 0, x_609);
lean_ctor_set(x_611, 1, x_610);
x_612 = l_Array_empty___closed__1;
x_613 = lean_array_push(x_612, x_611);
x_614 = l_Lean_Elab_Term_expandHave___closed__2;
x_615 = lean_array_push(x_613, x_614);
x_616 = lean_array_push(x_615, x_519);
x_617 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_609);
x_618 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_618, 0, x_609);
lean_ctor_set(x_618, 1, x_617);
x_619 = lean_array_push(x_612, x_618);
x_620 = l_Lean_Elab_Term_expandShow___closed__2;
lean_inc(x_609);
x_621 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_621, 0, x_609);
lean_ctor_set(x_621, 1, x_620);
x_622 = lean_array_push(x_612, x_621);
x_623 = lean_array_push(x_622, x_530);
x_624 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_624, 0, x_526);
lean_ctor_set(x_624, 1, x_623);
x_625 = lean_array_push(x_619, x_624);
x_626 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_626, 0, x_522);
lean_ctor_set(x_626, 1, x_625);
x_627 = lean_array_push(x_616, x_626);
x_628 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_629 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_629, 0, x_609);
lean_ctor_set(x_629, 1, x_628);
x_630 = lean_array_push(x_612, x_629);
x_631 = l_Lean_nullKind___closed__2;
x_632 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_632, 0, x_631);
lean_ctor_set(x_632, 1, x_630);
x_633 = lean_array_push(x_627, x_632);
x_634 = lean_array_push(x_633, x_606);
x_635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_635, 0, x_4);
lean_ctor_set(x_635, 1, x_634);
lean_ctor_set(x_607, 0, x_635);
return x_607;
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_636 = lean_ctor_get(x_607, 0);
x_637 = lean_ctor_get(x_607, 1);
lean_inc(x_637);
lean_inc(x_636);
lean_dec(x_607);
x_638 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_636);
x_639 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_639, 0, x_636);
lean_ctor_set(x_639, 1, x_638);
x_640 = l_Array_empty___closed__1;
x_641 = lean_array_push(x_640, x_639);
x_642 = l_Lean_Elab_Term_expandHave___closed__2;
x_643 = lean_array_push(x_641, x_642);
x_644 = lean_array_push(x_643, x_519);
x_645 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_636);
x_646 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_646, 0, x_636);
lean_ctor_set(x_646, 1, x_645);
x_647 = lean_array_push(x_640, x_646);
x_648 = l_Lean_Elab_Term_expandShow___closed__2;
lean_inc(x_636);
x_649 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_649, 0, x_636);
lean_ctor_set(x_649, 1, x_648);
x_650 = lean_array_push(x_640, x_649);
x_651 = lean_array_push(x_650, x_530);
x_652 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_652, 0, x_526);
lean_ctor_set(x_652, 1, x_651);
x_653 = lean_array_push(x_647, x_652);
x_654 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_654, 0, x_522);
lean_ctor_set(x_654, 1, x_653);
x_655 = lean_array_push(x_644, x_654);
x_656 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_657 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_657, 0, x_636);
lean_ctor_set(x_657, 1, x_656);
x_658 = lean_array_push(x_640, x_657);
x_659 = l_Lean_nullKind___closed__2;
x_660 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_660, 0, x_659);
lean_ctor_set(x_660, 1, x_658);
x_661 = lean_array_push(x_655, x_660);
x_662 = lean_array_push(x_661, x_606);
x_663 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_663, 0, x_4);
lean_ctor_set(x_663, 1, x_662);
x_664 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_664, 0, x_663);
lean_ctor_set(x_664, 1, x_637);
return x_664;
}
}
}
}
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; uint8_t x_668; 
x_665 = l_Lean_Syntax_getArg(x_521, x_8);
lean_dec(x_521);
x_666 = lean_unsigned_to_nat(4u);
x_667 = l_Lean_Syntax_getArg(x_1, x_666);
x_668 = l_Lean_Syntax_isNone(x_667);
if (x_668 == 0)
{
lean_object* x_669; uint8_t x_670; 
x_669 = l_Lean_nullKind___closed__2;
lean_inc(x_667);
x_670 = l_Lean_Syntax_isOfKind(x_667, x_669);
if (x_670 == 0)
{
lean_object* x_671; lean_object* x_672; 
lean_dec(x_667);
lean_dec(x_665);
lean_dec(x_519);
lean_dec(x_1);
x_671 = lean_box(1);
x_672 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_672, 0, x_671);
lean_ctor_set(x_672, 1, x_3);
return x_672;
}
else
{
lean_object* x_673; lean_object* x_674; uint8_t x_675; 
x_673 = l_Lean_Syntax_getArgs(x_667);
lean_dec(x_667);
x_674 = lean_array_get_size(x_673);
lean_dec(x_673);
x_675 = lean_nat_dec_eq(x_674, x_8);
lean_dec(x_674);
if (x_675 == 0)
{
lean_object* x_676; lean_object* x_677; 
lean_dec(x_665);
lean_dec(x_519);
lean_dec(x_1);
x_676 = lean_box(1);
x_677 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_677, 0, x_676);
lean_ctor_set(x_677, 1, x_3);
return x_677;
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; uint8_t x_683; 
x_678 = lean_unsigned_to_nat(5u);
x_679 = l_Lean_Syntax_getArg(x_1, x_678);
x_680 = l_Lean_Elab_Term_expandShow___closed__4;
x_681 = l_Lean_mkIdentFrom(x_1, x_680);
lean_dec(x_1);
x_682 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_683 = !lean_is_exclusive(x_682);
if (x_683 == 0)
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; 
x_684 = lean_ctor_get(x_682, 0);
x_685 = l_Lean_Parser_Tactic_let_x21___closed__1;
lean_inc(x_684);
x_686 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_686, 0, x_684);
lean_ctor_set(x_686, 1, x_685);
x_687 = l_Array_empty___closed__1;
x_688 = lean_array_push(x_687, x_686);
x_689 = lean_array_push(x_687, x_681);
x_690 = l_myMacro____x40_Init_Notation___hyg_12817____closed__10;
x_691 = lean_array_push(x_689, x_690);
x_692 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_684);
x_693 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_693, 0, x_684);
lean_ctor_set(x_693, 1, x_692);
x_694 = lean_array_push(x_687, x_693);
x_695 = lean_array_push(x_694, x_519);
x_696 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_697 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_697, 0, x_696);
lean_ctor_set(x_697, 1, x_695);
x_698 = lean_array_push(x_687, x_697);
x_699 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_699, 0, x_669);
lean_ctor_set(x_699, 1, x_698);
x_700 = lean_array_push(x_691, x_699);
x_701 = l_myMacro____x40_Init_Notation___hyg_13394____closed__11;
lean_inc(x_684);
x_702 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_702, 0, x_684);
lean_ctor_set(x_702, 1, x_701);
x_703 = lean_array_push(x_700, x_702);
x_704 = lean_array_push(x_703, x_665);
x_705 = l_myMacro____x40_Init_Notation___hyg_13394____closed__6;
x_706 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_704);
x_707 = lean_array_push(x_687, x_706);
x_708 = l_myMacro____x40_Init_Notation___hyg_13394____closed__4;
x_709 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_709, 0, x_708);
lean_ctor_set(x_709, 1, x_707);
x_710 = lean_array_push(x_688, x_709);
x_711 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_712 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_712, 0, x_684);
lean_ctor_set(x_712, 1, x_711);
x_713 = lean_array_push(x_687, x_712);
x_714 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_714, 0, x_669);
lean_ctor_set(x_714, 1, x_713);
x_715 = lean_array_push(x_710, x_714);
x_716 = lean_array_push(x_715, x_679);
x_717 = l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
x_718 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_718, 0, x_717);
lean_ctor_set(x_718, 1, x_716);
lean_ctor_set(x_682, 0, x_718);
return x_682;
}
else
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_719 = lean_ctor_get(x_682, 0);
x_720 = lean_ctor_get(x_682, 1);
lean_inc(x_720);
lean_inc(x_719);
lean_dec(x_682);
x_721 = l_Lean_Parser_Tactic_let_x21___closed__1;
lean_inc(x_719);
x_722 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_722, 0, x_719);
lean_ctor_set(x_722, 1, x_721);
x_723 = l_Array_empty___closed__1;
x_724 = lean_array_push(x_723, x_722);
x_725 = lean_array_push(x_723, x_681);
x_726 = l_myMacro____x40_Init_Notation___hyg_12817____closed__10;
x_727 = lean_array_push(x_725, x_726);
x_728 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_719);
x_729 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_729, 0, x_719);
lean_ctor_set(x_729, 1, x_728);
x_730 = lean_array_push(x_723, x_729);
x_731 = lean_array_push(x_730, x_519);
x_732 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_733 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_733, 0, x_732);
lean_ctor_set(x_733, 1, x_731);
x_734 = lean_array_push(x_723, x_733);
x_735 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_735, 0, x_669);
lean_ctor_set(x_735, 1, x_734);
x_736 = lean_array_push(x_727, x_735);
x_737 = l_myMacro____x40_Init_Notation___hyg_13394____closed__11;
lean_inc(x_719);
x_738 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_738, 0, x_719);
lean_ctor_set(x_738, 1, x_737);
x_739 = lean_array_push(x_736, x_738);
x_740 = lean_array_push(x_739, x_665);
x_741 = l_myMacro____x40_Init_Notation___hyg_13394____closed__6;
x_742 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_742, 0, x_741);
lean_ctor_set(x_742, 1, x_740);
x_743 = lean_array_push(x_723, x_742);
x_744 = l_myMacro____x40_Init_Notation___hyg_13394____closed__4;
x_745 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_745, 0, x_744);
lean_ctor_set(x_745, 1, x_743);
x_746 = lean_array_push(x_724, x_745);
x_747 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_748 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_748, 0, x_719);
lean_ctor_set(x_748, 1, x_747);
x_749 = lean_array_push(x_723, x_748);
x_750 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_750, 0, x_669);
lean_ctor_set(x_750, 1, x_749);
x_751 = lean_array_push(x_746, x_750);
x_752 = lean_array_push(x_751, x_679);
x_753 = l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
x_754 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_754, 0, x_753);
lean_ctor_set(x_754, 1, x_752);
x_755 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_755, 0, x_754);
lean_ctor_set(x_755, 1, x_720);
return x_755;
}
}
}
}
else
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; uint8_t x_761; 
lean_dec(x_667);
x_756 = lean_unsigned_to_nat(5u);
x_757 = l_Lean_Syntax_getArg(x_1, x_756);
x_758 = l_Lean_Elab_Term_expandShow___closed__4;
x_759 = l_Lean_mkIdentFrom(x_1, x_758);
lean_dec(x_1);
x_760 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_761 = !lean_is_exclusive(x_760);
if (x_761 == 0)
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; 
x_762 = lean_ctor_get(x_760, 0);
x_763 = l_Lean_Parser_Tactic_let_x21___closed__1;
lean_inc(x_762);
x_764 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_764, 0, x_762);
lean_ctor_set(x_764, 1, x_763);
x_765 = l_Array_empty___closed__1;
x_766 = lean_array_push(x_765, x_764);
x_767 = lean_array_push(x_765, x_759);
x_768 = l_myMacro____x40_Init_Notation___hyg_1192____closed__8;
x_769 = lean_array_push(x_767, x_768);
x_770 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_762);
x_771 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_771, 0, x_762);
lean_ctor_set(x_771, 1, x_770);
x_772 = lean_array_push(x_765, x_771);
x_773 = lean_array_push(x_772, x_519);
x_774 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_775 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_775, 0, x_774);
lean_ctor_set(x_775, 1, x_773);
x_776 = lean_array_push(x_765, x_775);
x_777 = l_Lean_nullKind___closed__2;
x_778 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_778, 0, x_777);
lean_ctor_set(x_778, 1, x_776);
x_779 = lean_array_push(x_769, x_778);
x_780 = l_myMacro____x40_Init_Notation___hyg_13394____closed__11;
lean_inc(x_762);
x_781 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_781, 0, x_762);
lean_ctor_set(x_781, 1, x_780);
x_782 = lean_array_push(x_779, x_781);
x_783 = lean_array_push(x_782, x_665);
x_784 = l_myMacro____x40_Init_Notation___hyg_13394____closed__6;
x_785 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_785, 0, x_784);
lean_ctor_set(x_785, 1, x_783);
x_786 = lean_array_push(x_765, x_785);
x_787 = l_myMacro____x40_Init_Notation___hyg_13394____closed__4;
x_788 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_788, 0, x_787);
lean_ctor_set(x_788, 1, x_786);
x_789 = lean_array_push(x_766, x_788);
x_790 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_791 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_791, 0, x_762);
lean_ctor_set(x_791, 1, x_790);
x_792 = lean_array_push(x_765, x_791);
x_793 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_793, 0, x_777);
lean_ctor_set(x_793, 1, x_792);
x_794 = lean_array_push(x_789, x_793);
x_795 = lean_array_push(x_794, x_757);
x_796 = l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
x_797 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_797, 0, x_796);
lean_ctor_set(x_797, 1, x_795);
lean_ctor_set(x_760, 0, x_797);
return x_760;
}
else
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; 
x_798 = lean_ctor_get(x_760, 0);
x_799 = lean_ctor_get(x_760, 1);
lean_inc(x_799);
lean_inc(x_798);
lean_dec(x_760);
x_800 = l_Lean_Parser_Tactic_let_x21___closed__1;
lean_inc(x_798);
x_801 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_801, 0, x_798);
lean_ctor_set(x_801, 1, x_800);
x_802 = l_Array_empty___closed__1;
x_803 = lean_array_push(x_802, x_801);
x_804 = lean_array_push(x_802, x_759);
x_805 = l_myMacro____x40_Init_Notation___hyg_1192____closed__8;
x_806 = lean_array_push(x_804, x_805);
x_807 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_798);
x_808 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_808, 0, x_798);
lean_ctor_set(x_808, 1, x_807);
x_809 = lean_array_push(x_802, x_808);
x_810 = lean_array_push(x_809, x_519);
x_811 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_812 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_812, 0, x_811);
lean_ctor_set(x_812, 1, x_810);
x_813 = lean_array_push(x_802, x_812);
x_814 = l_Lean_nullKind___closed__2;
x_815 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_815, 0, x_814);
lean_ctor_set(x_815, 1, x_813);
x_816 = lean_array_push(x_806, x_815);
x_817 = l_myMacro____x40_Init_Notation___hyg_13394____closed__11;
lean_inc(x_798);
x_818 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_818, 0, x_798);
lean_ctor_set(x_818, 1, x_817);
x_819 = lean_array_push(x_816, x_818);
x_820 = lean_array_push(x_819, x_665);
x_821 = l_myMacro____x40_Init_Notation___hyg_13394____closed__6;
x_822 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_822, 0, x_821);
lean_ctor_set(x_822, 1, x_820);
x_823 = lean_array_push(x_802, x_822);
x_824 = l_myMacro____x40_Init_Notation___hyg_13394____closed__4;
x_825 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_825, 0, x_824);
lean_ctor_set(x_825, 1, x_823);
x_826 = lean_array_push(x_803, x_825);
x_827 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_828 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_828, 0, x_798);
lean_ctor_set(x_828, 1, x_827);
x_829 = lean_array_push(x_802, x_828);
x_830 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_830, 0, x_814);
lean_ctor_set(x_830, 1, x_829);
x_831 = lean_array_push(x_826, x_830);
x_832 = lean_array_push(x_831, x_757);
x_833 = l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
x_834 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_834, 0, x_833);
lean_ctor_set(x_834, 1, x_832);
x_835 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_835, 0, x_834);
lean_ctor_set(x_835, 1, x_799);
return x_835;
}
}
}
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; uint8_t x_839; 
x_836 = l_Lean_Syntax_getArg(x_521, x_8);
lean_dec(x_521);
x_837 = lean_unsigned_to_nat(4u);
x_838 = l_Lean_Syntax_getArg(x_1, x_837);
x_839 = l_Lean_Syntax_isNone(x_838);
if (x_839 == 0)
{
lean_object* x_840; uint8_t x_841; 
x_840 = l_Lean_nullKind___closed__2;
lean_inc(x_838);
x_841 = l_Lean_Syntax_isOfKind(x_838, x_840);
if (x_841 == 0)
{
lean_object* x_842; lean_object* x_843; 
lean_dec(x_838);
lean_dec(x_836);
lean_dec(x_519);
lean_dec(x_1);
x_842 = lean_box(1);
x_843 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_843, 0, x_842);
lean_ctor_set(x_843, 1, x_3);
return x_843;
}
else
{
lean_object* x_844; lean_object* x_845; uint8_t x_846; 
x_844 = l_Lean_Syntax_getArgs(x_838);
lean_dec(x_838);
x_845 = lean_array_get_size(x_844);
lean_dec(x_844);
x_846 = lean_nat_dec_eq(x_845, x_8);
lean_dec(x_845);
if (x_846 == 0)
{
lean_object* x_847; lean_object* x_848; 
lean_dec(x_836);
lean_dec(x_519);
lean_dec(x_1);
x_847 = lean_box(1);
x_848 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_848, 0, x_847);
lean_ctor_set(x_848, 1, x_3);
return x_848;
}
else
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; uint8_t x_854; 
x_849 = lean_unsigned_to_nat(5u);
x_850 = l_Lean_Syntax_getArg(x_1, x_849);
x_851 = l_Lean_Elab_Term_expandShow___closed__4;
x_852 = l_Lean_mkIdentFrom(x_1, x_851);
lean_dec(x_1);
x_853 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_854 = !lean_is_exclusive(x_853);
if (x_854 == 0)
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; 
x_855 = lean_ctor_get(x_853, 0);
x_856 = l_Lean_Parser_Tactic_let_x21___closed__1;
lean_inc(x_855);
x_857 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_857, 0, x_855);
lean_ctor_set(x_857, 1, x_856);
x_858 = l_Array_empty___closed__1;
x_859 = lean_array_push(x_858, x_857);
x_860 = lean_array_push(x_858, x_852);
x_861 = l_myMacro____x40_Init_Notation___hyg_12817____closed__10;
x_862 = lean_array_push(x_860, x_861);
x_863 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_855);
x_864 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_864, 0, x_855);
lean_ctor_set(x_864, 1, x_863);
x_865 = lean_array_push(x_858, x_864);
x_866 = lean_array_push(x_865, x_519);
x_867 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_868 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_868, 0, x_867);
lean_ctor_set(x_868, 1, x_866);
x_869 = lean_array_push(x_858, x_868);
x_870 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_870, 0, x_840);
lean_ctor_set(x_870, 1, x_869);
x_871 = lean_array_push(x_862, x_870);
x_872 = l_myMacro____x40_Init_Notation___hyg_13394____closed__11;
lean_inc(x_855);
x_873 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_873, 0, x_855);
lean_ctor_set(x_873, 1, x_872);
x_874 = lean_array_push(x_871, x_873);
x_875 = lean_array_push(x_874, x_836);
x_876 = l_myMacro____x40_Init_Notation___hyg_13394____closed__6;
x_877 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_877, 0, x_876);
lean_ctor_set(x_877, 1, x_875);
x_878 = lean_array_push(x_858, x_877);
x_879 = l_myMacro____x40_Init_Notation___hyg_13394____closed__4;
x_880 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_880, 0, x_879);
lean_ctor_set(x_880, 1, x_878);
x_881 = lean_array_push(x_859, x_880);
x_882 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_883 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_883, 0, x_855);
lean_ctor_set(x_883, 1, x_882);
x_884 = lean_array_push(x_858, x_883);
x_885 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_885, 0, x_840);
lean_ctor_set(x_885, 1, x_884);
x_886 = lean_array_push(x_881, x_885);
x_887 = lean_array_push(x_886, x_850);
x_888 = l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
x_889 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_889, 0, x_888);
lean_ctor_set(x_889, 1, x_887);
lean_ctor_set(x_853, 0, x_889);
return x_853;
}
else
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; 
x_890 = lean_ctor_get(x_853, 0);
x_891 = lean_ctor_get(x_853, 1);
lean_inc(x_891);
lean_inc(x_890);
lean_dec(x_853);
x_892 = l_Lean_Parser_Tactic_let_x21___closed__1;
lean_inc(x_890);
x_893 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_893, 0, x_890);
lean_ctor_set(x_893, 1, x_892);
x_894 = l_Array_empty___closed__1;
x_895 = lean_array_push(x_894, x_893);
x_896 = lean_array_push(x_894, x_852);
x_897 = l_myMacro____x40_Init_Notation___hyg_12817____closed__10;
x_898 = lean_array_push(x_896, x_897);
x_899 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_890);
x_900 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_900, 0, x_890);
lean_ctor_set(x_900, 1, x_899);
x_901 = lean_array_push(x_894, x_900);
x_902 = lean_array_push(x_901, x_519);
x_903 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_904 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_904, 0, x_903);
lean_ctor_set(x_904, 1, x_902);
x_905 = lean_array_push(x_894, x_904);
x_906 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_906, 0, x_840);
lean_ctor_set(x_906, 1, x_905);
x_907 = lean_array_push(x_898, x_906);
x_908 = l_myMacro____x40_Init_Notation___hyg_13394____closed__11;
lean_inc(x_890);
x_909 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_909, 0, x_890);
lean_ctor_set(x_909, 1, x_908);
x_910 = lean_array_push(x_907, x_909);
x_911 = lean_array_push(x_910, x_836);
x_912 = l_myMacro____x40_Init_Notation___hyg_13394____closed__6;
x_913 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_913, 0, x_912);
lean_ctor_set(x_913, 1, x_911);
x_914 = lean_array_push(x_894, x_913);
x_915 = l_myMacro____x40_Init_Notation___hyg_13394____closed__4;
x_916 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_916, 0, x_915);
lean_ctor_set(x_916, 1, x_914);
x_917 = lean_array_push(x_895, x_916);
x_918 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_919 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_919, 0, x_890);
lean_ctor_set(x_919, 1, x_918);
x_920 = lean_array_push(x_894, x_919);
x_921 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_921, 0, x_840);
lean_ctor_set(x_921, 1, x_920);
x_922 = lean_array_push(x_917, x_921);
x_923 = lean_array_push(x_922, x_850);
x_924 = l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
x_925 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_925, 0, x_924);
lean_ctor_set(x_925, 1, x_923);
x_926 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_926, 0, x_925);
lean_ctor_set(x_926, 1, x_891);
return x_926;
}
}
}
}
else
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; uint8_t x_932; 
lean_dec(x_838);
x_927 = lean_unsigned_to_nat(5u);
x_928 = l_Lean_Syntax_getArg(x_1, x_927);
x_929 = l_Lean_Elab_Term_expandShow___closed__4;
x_930 = l_Lean_mkIdentFrom(x_1, x_929);
lean_dec(x_1);
x_931 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_932 = !lean_is_exclusive(x_931);
if (x_932 == 0)
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; 
x_933 = lean_ctor_get(x_931, 0);
x_934 = l_Lean_Parser_Tactic_let_x21___closed__1;
lean_inc(x_933);
x_935 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_935, 0, x_933);
lean_ctor_set(x_935, 1, x_934);
x_936 = l_Array_empty___closed__1;
x_937 = lean_array_push(x_936, x_935);
x_938 = lean_array_push(x_936, x_930);
x_939 = l_myMacro____x40_Init_Notation___hyg_1192____closed__8;
x_940 = lean_array_push(x_938, x_939);
x_941 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_933);
x_942 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_942, 0, x_933);
lean_ctor_set(x_942, 1, x_941);
x_943 = lean_array_push(x_936, x_942);
x_944 = lean_array_push(x_943, x_519);
x_945 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_946 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_946, 0, x_945);
lean_ctor_set(x_946, 1, x_944);
x_947 = lean_array_push(x_936, x_946);
x_948 = l_Lean_nullKind___closed__2;
x_949 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_949, 0, x_948);
lean_ctor_set(x_949, 1, x_947);
x_950 = lean_array_push(x_940, x_949);
x_951 = l_myMacro____x40_Init_Notation___hyg_13394____closed__11;
lean_inc(x_933);
x_952 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_952, 0, x_933);
lean_ctor_set(x_952, 1, x_951);
x_953 = lean_array_push(x_950, x_952);
x_954 = lean_array_push(x_953, x_836);
x_955 = l_myMacro____x40_Init_Notation___hyg_13394____closed__6;
x_956 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_956, 0, x_955);
lean_ctor_set(x_956, 1, x_954);
x_957 = lean_array_push(x_936, x_956);
x_958 = l_myMacro____x40_Init_Notation___hyg_13394____closed__4;
x_959 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_959, 0, x_958);
lean_ctor_set(x_959, 1, x_957);
x_960 = lean_array_push(x_937, x_959);
x_961 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_962 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_962, 0, x_933);
lean_ctor_set(x_962, 1, x_961);
x_963 = lean_array_push(x_936, x_962);
x_964 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_964, 0, x_948);
lean_ctor_set(x_964, 1, x_963);
x_965 = lean_array_push(x_960, x_964);
x_966 = lean_array_push(x_965, x_928);
x_967 = l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
x_968 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_968, 0, x_967);
lean_ctor_set(x_968, 1, x_966);
lean_ctor_set(x_931, 0, x_968);
return x_931;
}
else
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
x_969 = lean_ctor_get(x_931, 0);
x_970 = lean_ctor_get(x_931, 1);
lean_inc(x_970);
lean_inc(x_969);
lean_dec(x_931);
x_971 = l_Lean_Parser_Tactic_let_x21___closed__1;
lean_inc(x_969);
x_972 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_972, 0, x_969);
lean_ctor_set(x_972, 1, x_971);
x_973 = l_Array_empty___closed__1;
x_974 = lean_array_push(x_973, x_972);
x_975 = lean_array_push(x_973, x_930);
x_976 = l_myMacro____x40_Init_Notation___hyg_1192____closed__8;
x_977 = lean_array_push(x_975, x_976);
x_978 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_969);
x_979 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_979, 0, x_969);
lean_ctor_set(x_979, 1, x_978);
x_980 = lean_array_push(x_973, x_979);
x_981 = lean_array_push(x_980, x_519);
x_982 = l_Lean_expandExplicitBindersAux_loop___closed__4;
x_983 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_983, 0, x_982);
lean_ctor_set(x_983, 1, x_981);
x_984 = lean_array_push(x_973, x_983);
x_985 = l_Lean_nullKind___closed__2;
x_986 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_986, 0, x_985);
lean_ctor_set(x_986, 1, x_984);
x_987 = lean_array_push(x_977, x_986);
x_988 = l_myMacro____x40_Init_Notation___hyg_13394____closed__11;
lean_inc(x_969);
x_989 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_989, 0, x_969);
lean_ctor_set(x_989, 1, x_988);
x_990 = lean_array_push(x_987, x_989);
x_991 = lean_array_push(x_990, x_836);
x_992 = l_myMacro____x40_Init_Notation___hyg_13394____closed__6;
x_993 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_993, 0, x_992);
lean_ctor_set(x_993, 1, x_991);
x_994 = lean_array_push(x_973, x_993);
x_995 = l_myMacro____x40_Init_Notation___hyg_13394____closed__4;
x_996 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_996, 0, x_995);
lean_ctor_set(x_996, 1, x_994);
x_997 = lean_array_push(x_974, x_996);
x_998 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_999 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_999, 0, x_969);
lean_ctor_set(x_999, 1, x_998);
x_1000 = lean_array_push(x_973, x_999);
x_1001 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1001, 0, x_985);
lean_ctor_set(x_1001, 1, x_1000);
x_1002 = lean_array_push(x_997, x_1001);
x_1003 = lean_array_push(x_1002, x_928);
x_1004 = l_Lean_Parser_Term_let_x21___elambda__1___closed__1;
x_1005 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1005, 0, x_1004);
lean_ctor_set(x_1005, 1, x_1003);
x_1006 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1006, 0, x_1005);
lean_ctor_set(x_1006, 1, x_970);
return x_1006;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_expandHave___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandHave(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandHave___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandHave___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandHave(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_Lean_Parser_Term_have___elambda__1___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandHave___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandSuffices_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_expandSuffices_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSuffices_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandSuffices_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_expandSuffices_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSuffices_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandSuffices_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_expandSuffices_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSuffices_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandSuffices_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_expandSuffices_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSuffices_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandSuffices_match__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_expandSuffices_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSuffices_match__5___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandSuffices_match__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_expandSuffices_match__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSuffices_match__6___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandSuffices_match__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_expandSuffices_match__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSuffices_match__7___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandSuffices_match__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_expandSuffices_match__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSuffices_match__8___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandSuffices(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Term_suffices___elambda__1___closed__1;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_isNone(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_nullKind___closed__2;
lean_inc(x_9);
x_12 = l_Lean_Syntax_isOfKind(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_1);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = l_Lean_Syntax_getArgs(x_9);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_1);
x_19 = lean_box(1);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_9, x_21);
lean_dec(x_9);
x_23 = l_Lean_Syntax_getArg(x_1, x_17);
x_24 = lean_unsigned_to_nat(3u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
x_26 = l_Lean_Parser_Term_fromTerm___elambda__1___closed__2;
lean_inc(x_25);
x_27 = l_Lean_Syntax_isOfKind(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Parser_Term_byTactic___elambda__1___closed__2;
lean_inc(x_25);
x_29 = l_Lean_Syntax_isOfKind(x_25, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_30 = lean_box(1);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = l_Lean_Syntax_getArg(x_25, x_8);
lean_dec(x_25);
x_33 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_14558____closed__3;
lean_inc(x_32);
x_34 = l_Lean_Syntax_isOfKind(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_35 = lean_box(1);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_3);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_unsigned_to_nat(4u);
x_38 = l_Lean_Syntax_getArg(x_1, x_37);
x_39 = l_Lean_Syntax_isNone(x_38);
if (x_39 == 0)
{
uint8_t x_40; 
lean_inc(x_38);
x_40 = l_Lean_Syntax_isOfKind(x_38, x_11);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_41 = lean_box(1);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_3);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = l_Lean_Syntax_getArgs(x_38);
lean_dec(x_38);
x_44 = lean_array_get_size(x_43);
lean_dec(x_43);
x_45 = lean_nat_dec_eq(x_44, x_8);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_46 = lean_box(1);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_3);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_unsigned_to_nat(5u);
x_49 = l_Lean_Syntax_getArg(x_1, x_48);
lean_dec(x_1);
x_50 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_52);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Array_empty___closed__1;
x_56 = lean_array_push(x_55, x_54);
x_57 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_52);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Syntax_mkApp___closed__1;
x_60 = lean_array_push(x_59, x_22);
x_61 = lean_array_push(x_60, x_58);
x_62 = l_Array_appendCore___rarg(x_55, x_61);
lean_dec(x_61);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_11);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_array_push(x_56, x_63);
x_65 = lean_array_push(x_64, x_23);
x_66 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_52);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_52);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_array_push(x_55, x_67);
x_69 = lean_array_push(x_68, x_49);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_26);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_array_push(x_65, x_70);
x_72 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
lean_inc(x_52);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_52);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_array_push(x_55, x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_11);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_array_push(x_71, x_75);
x_77 = l_Lean_Elab_Term_expandShow___closed__2;
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_52);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_array_push(x_55, x_78);
x_80 = lean_array_push(x_79, x_32);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_28);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_array_push(x_76, x_81);
x_83 = l_Lean_Parser_Term_have___elambda__1___closed__1;
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_50, 0, x_84);
return x_50;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_85 = lean_ctor_get(x_50, 0);
x_86 = lean_ctor_get(x_50, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_50);
x_87 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_85);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Array_empty___closed__1;
x_90 = lean_array_push(x_89, x_88);
x_91 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_85);
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_85);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_Syntax_mkApp___closed__1;
x_94 = lean_array_push(x_93, x_22);
x_95 = lean_array_push(x_94, x_92);
x_96 = l_Array_appendCore___rarg(x_89, x_95);
lean_dec(x_95);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_11);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_array_push(x_90, x_97);
x_99 = lean_array_push(x_98, x_23);
x_100 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_85);
x_101 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_101, 0, x_85);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_array_push(x_89, x_101);
x_103 = lean_array_push(x_102, x_49);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_26);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_array_push(x_99, x_104);
x_106 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
lean_inc(x_85);
x_107 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_107, 0, x_85);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_array_push(x_89, x_107);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_11);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_array_push(x_105, x_109);
x_111 = l_Lean_Elab_Term_expandShow___closed__2;
x_112 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_112, 0, x_85);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_array_push(x_89, x_112);
x_114 = lean_array_push(x_113, x_32);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_28);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_array_push(x_110, x_115);
x_117 = l_Lean_Parser_Term_have___elambda__1___closed__1;
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_86);
return x_119;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
lean_dec(x_38);
x_120 = lean_unsigned_to_nat(5u);
x_121 = l_Lean_Syntax_getArg(x_1, x_120);
lean_dec(x_1);
x_122 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_124 = lean_ctor_get(x_122, 0);
x_125 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_124);
x_126 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Array_empty___closed__1;
x_128 = lean_array_push(x_127, x_126);
x_129 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_124);
x_130 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_130, 0, x_124);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_Syntax_mkApp___closed__1;
x_132 = lean_array_push(x_131, x_22);
x_133 = lean_array_push(x_132, x_130);
x_134 = l_Array_appendCore___rarg(x_127, x_133);
lean_dec(x_133);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_11);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_array_push(x_128, x_135);
x_137 = lean_array_push(x_136, x_23);
x_138 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_124);
x_139 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_139, 0, x_124);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_array_push(x_127, x_139);
x_141 = lean_array_push(x_140, x_121);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_26);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_array_push(x_137, x_142);
x_144 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
lean_inc(x_124);
x_145 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_145, 0, x_124);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_array_push(x_127, x_145);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_11);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_array_push(x_143, x_147);
x_149 = l_Lean_Elab_Term_expandShow___closed__2;
x_150 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_150, 0, x_124);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_array_push(x_127, x_150);
x_152 = lean_array_push(x_151, x_32);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_28);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_array_push(x_148, x_153);
x_155 = l_Lean_Parser_Term_have___elambda__1___closed__1;
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
lean_ctor_set(x_122, 0, x_156);
return x_122;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_157 = lean_ctor_get(x_122, 0);
x_158 = lean_ctor_get(x_122, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_122);
x_159 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_157);
x_160 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Array_empty___closed__1;
x_162 = lean_array_push(x_161, x_160);
x_163 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_157);
x_164 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_164, 0, x_157);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Lean_Syntax_mkApp___closed__1;
x_166 = lean_array_push(x_165, x_22);
x_167 = lean_array_push(x_166, x_164);
x_168 = l_Array_appendCore___rarg(x_161, x_167);
lean_dec(x_167);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_11);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_array_push(x_162, x_169);
x_171 = lean_array_push(x_170, x_23);
x_172 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_157);
x_173 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_173, 0, x_157);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_array_push(x_161, x_173);
x_175 = lean_array_push(x_174, x_121);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_26);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_array_push(x_171, x_176);
x_178 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
lean_inc(x_157);
x_179 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_179, 0, x_157);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_array_push(x_161, x_179);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_11);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_array_push(x_177, x_181);
x_183 = l_Lean_Elab_Term_expandShow___closed__2;
x_184 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_184, 0, x_157);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_array_push(x_161, x_184);
x_186 = lean_array_push(x_185, x_32);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_28);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_array_push(x_182, x_187);
x_189 = l_Lean_Parser_Term_have___elambda__1___closed__1;
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_158);
return x_191;
}
}
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_192 = l_Lean_Syntax_getArg(x_25, x_8);
lean_dec(x_25);
x_193 = lean_unsigned_to_nat(4u);
x_194 = l_Lean_Syntax_getArg(x_1, x_193);
x_195 = l_Lean_Syntax_isNone(x_194);
if (x_195 == 0)
{
uint8_t x_196; 
lean_inc(x_194);
x_196 = l_Lean_Syntax_isOfKind(x_194, x_11);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_194);
lean_dec(x_192);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_197 = lean_box(1);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_3);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_199 = l_Lean_Syntax_getArgs(x_194);
lean_dec(x_194);
x_200 = lean_array_get_size(x_199);
lean_dec(x_199);
x_201 = lean_nat_dec_eq(x_200, x_8);
lean_dec(x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_192);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_202 = lean_box(1);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_3);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_204 = lean_unsigned_to_nat(5u);
x_205 = l_Lean_Syntax_getArg(x_1, x_204);
lean_dec(x_1);
x_206 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_207 = !lean_is_exclusive(x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_208 = lean_ctor_get(x_206, 0);
x_209 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_208);
x_210 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = l_Array_empty___closed__1;
x_212 = lean_array_push(x_211, x_210);
x_213 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_208);
x_214 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_214, 0, x_208);
lean_ctor_set(x_214, 1, x_213);
x_215 = l_Lean_Syntax_mkApp___closed__1;
x_216 = lean_array_push(x_215, x_22);
x_217 = lean_array_push(x_216, x_214);
x_218 = l_Array_appendCore___rarg(x_211, x_217);
lean_dec(x_217);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_11);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_array_push(x_212, x_219);
x_221 = lean_array_push(x_220, x_23);
x_222 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_208);
x_223 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_223, 0, x_208);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_array_push(x_211, x_223);
x_225 = lean_array_push(x_224, x_205);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_26);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_array_push(x_221, x_226);
x_228 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_229 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_229, 0, x_208);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_array_push(x_211, x_229);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_11);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_array_push(x_227, x_231);
x_233 = lean_array_push(x_232, x_192);
x_234 = l_Lean_Parser_Term_have___elambda__1___closed__1;
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_233);
lean_ctor_set(x_206, 0, x_235);
return x_206;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_236 = lean_ctor_get(x_206, 0);
x_237 = lean_ctor_get(x_206, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_206);
x_238 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_236);
x_239 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_238);
x_240 = l_Array_empty___closed__1;
x_241 = lean_array_push(x_240, x_239);
x_242 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_236);
x_243 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_243, 0, x_236);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Lean_Syntax_mkApp___closed__1;
x_245 = lean_array_push(x_244, x_22);
x_246 = lean_array_push(x_245, x_243);
x_247 = l_Array_appendCore___rarg(x_240, x_246);
lean_dec(x_246);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_11);
lean_ctor_set(x_248, 1, x_247);
x_249 = lean_array_push(x_241, x_248);
x_250 = lean_array_push(x_249, x_23);
x_251 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_236);
x_252 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_252, 0, x_236);
lean_ctor_set(x_252, 1, x_251);
x_253 = lean_array_push(x_240, x_252);
x_254 = lean_array_push(x_253, x_205);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_26);
lean_ctor_set(x_255, 1, x_254);
x_256 = lean_array_push(x_250, x_255);
x_257 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_258 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_258, 0, x_236);
lean_ctor_set(x_258, 1, x_257);
x_259 = lean_array_push(x_240, x_258);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_11);
lean_ctor_set(x_260, 1, x_259);
x_261 = lean_array_push(x_256, x_260);
x_262 = lean_array_push(x_261, x_192);
x_263 = l_Lean_Parser_Term_have___elambda__1___closed__1;
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_262);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_237);
return x_265;
}
}
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
lean_dec(x_194);
x_266 = lean_unsigned_to_nat(5u);
x_267 = l_Lean_Syntax_getArg(x_1, x_266);
lean_dec(x_1);
x_268 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_270 = lean_ctor_get(x_268, 0);
x_271 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_270);
x_272 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
x_273 = l_Array_empty___closed__1;
x_274 = lean_array_push(x_273, x_272);
x_275 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_270);
x_276 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_276, 0, x_270);
lean_ctor_set(x_276, 1, x_275);
x_277 = l_Lean_Syntax_mkApp___closed__1;
x_278 = lean_array_push(x_277, x_22);
x_279 = lean_array_push(x_278, x_276);
x_280 = l_Array_appendCore___rarg(x_273, x_279);
lean_dec(x_279);
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_11);
lean_ctor_set(x_281, 1, x_280);
x_282 = lean_array_push(x_274, x_281);
x_283 = lean_array_push(x_282, x_23);
x_284 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_270);
x_285 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_285, 0, x_270);
lean_ctor_set(x_285, 1, x_284);
x_286 = lean_array_push(x_273, x_285);
x_287 = lean_array_push(x_286, x_267);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_26);
lean_ctor_set(x_288, 1, x_287);
x_289 = lean_array_push(x_283, x_288);
x_290 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_291 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_291, 0, x_270);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_array_push(x_273, x_291);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_11);
lean_ctor_set(x_293, 1, x_292);
x_294 = lean_array_push(x_289, x_293);
x_295 = lean_array_push(x_294, x_192);
x_296 = l_Lean_Parser_Term_have___elambda__1___closed__1;
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_295);
lean_ctor_set(x_268, 0, x_297);
return x_268;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_298 = lean_ctor_get(x_268, 0);
x_299 = lean_ctor_get(x_268, 1);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_268);
x_300 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_298);
x_301 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_300);
x_302 = l_Array_empty___closed__1;
x_303 = lean_array_push(x_302, x_301);
x_304 = l_myMacro____x40_Init_Notation___hyg_12817____closed__9;
lean_inc(x_298);
x_305 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_305, 0, x_298);
lean_ctor_set(x_305, 1, x_304);
x_306 = l_Lean_Syntax_mkApp___closed__1;
x_307 = lean_array_push(x_306, x_22);
x_308 = lean_array_push(x_307, x_305);
x_309 = l_Array_appendCore___rarg(x_302, x_308);
lean_dec(x_308);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_11);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_array_push(x_303, x_310);
x_312 = lean_array_push(x_311, x_23);
x_313 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_298);
x_314 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_314, 0, x_298);
lean_ctor_set(x_314, 1, x_313);
x_315 = lean_array_push(x_302, x_314);
x_316 = lean_array_push(x_315, x_267);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_26);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_array_push(x_312, x_317);
x_319 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_320 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_320, 0, x_298);
lean_ctor_set(x_320, 1, x_319);
x_321 = lean_array_push(x_302, x_320);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_11);
lean_ctor_set(x_322, 1, x_321);
x_323 = lean_array_push(x_318, x_322);
x_324 = lean_array_push(x_323, x_192);
x_325 = l_Lean_Parser_Term_have___elambda__1___closed__1;
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_324);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_299);
return x_327;
}
}
}
}
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; 
lean_dec(x_9);
x_328 = lean_unsigned_to_nat(2u);
x_329 = l_Lean_Syntax_getArg(x_1, x_328);
x_330 = lean_unsigned_to_nat(3u);
x_331 = l_Lean_Syntax_getArg(x_1, x_330);
x_332 = l_Lean_Parser_Term_fromTerm___elambda__1___closed__2;
lean_inc(x_331);
x_333 = l_Lean_Syntax_isOfKind(x_331, x_332);
if (x_333 == 0)
{
lean_object* x_334; uint8_t x_335; 
x_334 = l_Lean_Parser_Term_byTactic___elambda__1___closed__2;
lean_inc(x_331);
x_335 = l_Lean_Syntax_isOfKind(x_331, x_334);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_331);
lean_dec(x_329);
lean_dec(x_1);
x_336 = lean_box(1);
x_337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_3);
return x_337;
}
else
{
lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_338 = l_Lean_Syntax_getArg(x_331, x_8);
lean_dec(x_331);
x_339 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_14558____closed__3;
lean_inc(x_338);
x_340 = l_Lean_Syntax_isOfKind(x_338, x_339);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; 
lean_dec(x_338);
lean_dec(x_329);
lean_dec(x_1);
x_341 = lean_box(1);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_3);
return x_342;
}
else
{
lean_object* x_343; lean_object* x_344; uint8_t x_345; 
x_343 = lean_unsigned_to_nat(4u);
x_344 = l_Lean_Syntax_getArg(x_1, x_343);
x_345 = l_Lean_Syntax_isNone(x_344);
if (x_345 == 0)
{
lean_object* x_346; uint8_t x_347; 
x_346 = l_Lean_nullKind___closed__2;
lean_inc(x_344);
x_347 = l_Lean_Syntax_isOfKind(x_344, x_346);
if (x_347 == 0)
{
lean_object* x_348; lean_object* x_349; 
lean_dec(x_344);
lean_dec(x_338);
lean_dec(x_329);
lean_dec(x_1);
x_348 = lean_box(1);
x_349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_3);
return x_349;
}
else
{
lean_object* x_350; lean_object* x_351; uint8_t x_352; 
x_350 = l_Lean_Syntax_getArgs(x_344);
lean_dec(x_344);
x_351 = lean_array_get_size(x_350);
lean_dec(x_350);
x_352 = lean_nat_dec_eq(x_351, x_8);
lean_dec(x_351);
if (x_352 == 0)
{
lean_object* x_353; lean_object* x_354; 
lean_dec(x_338);
lean_dec(x_329);
lean_dec(x_1);
x_353 = lean_box(1);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_3);
return x_354;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; 
x_355 = lean_unsigned_to_nat(5u);
x_356 = l_Lean_Syntax_getArg(x_1, x_355);
lean_dec(x_1);
x_357 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_358 = !lean_is_exclusive(x_357);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_359 = lean_ctor_get(x_357, 0);
x_360 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_359);
x_361 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_360);
x_362 = l_Array_empty___closed__1;
x_363 = lean_array_push(x_362, x_361);
x_364 = l_Lean_Elab_Term_expandHave___closed__2;
x_365 = lean_array_push(x_363, x_364);
x_366 = lean_array_push(x_365, x_329);
x_367 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_359);
x_368 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_368, 0, x_359);
lean_ctor_set(x_368, 1, x_367);
x_369 = lean_array_push(x_362, x_368);
x_370 = lean_array_push(x_369, x_356);
x_371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_371, 0, x_332);
lean_ctor_set(x_371, 1, x_370);
x_372 = lean_array_push(x_366, x_371);
x_373 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
lean_inc(x_359);
x_374 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_374, 0, x_359);
lean_ctor_set(x_374, 1, x_373);
x_375 = lean_array_push(x_362, x_374);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_346);
lean_ctor_set(x_376, 1, x_375);
x_377 = lean_array_push(x_372, x_376);
x_378 = l_Lean_Elab_Term_expandShow___closed__2;
x_379 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_379, 0, x_359);
lean_ctor_set(x_379, 1, x_378);
x_380 = lean_array_push(x_362, x_379);
x_381 = lean_array_push(x_380, x_338);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_334);
lean_ctor_set(x_382, 1, x_381);
x_383 = lean_array_push(x_377, x_382);
x_384 = l_Lean_Parser_Term_have___elambda__1___closed__1;
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_383);
lean_ctor_set(x_357, 0, x_385);
return x_357;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_386 = lean_ctor_get(x_357, 0);
x_387 = lean_ctor_get(x_357, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_357);
x_388 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_386);
x_389 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_388);
x_390 = l_Array_empty___closed__1;
x_391 = lean_array_push(x_390, x_389);
x_392 = l_Lean_Elab_Term_expandHave___closed__2;
x_393 = lean_array_push(x_391, x_392);
x_394 = lean_array_push(x_393, x_329);
x_395 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_386);
x_396 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_396, 0, x_386);
lean_ctor_set(x_396, 1, x_395);
x_397 = lean_array_push(x_390, x_396);
x_398 = lean_array_push(x_397, x_356);
x_399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_399, 0, x_332);
lean_ctor_set(x_399, 1, x_398);
x_400 = lean_array_push(x_394, x_399);
x_401 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
lean_inc(x_386);
x_402 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_402, 0, x_386);
lean_ctor_set(x_402, 1, x_401);
x_403 = lean_array_push(x_390, x_402);
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_346);
lean_ctor_set(x_404, 1, x_403);
x_405 = lean_array_push(x_400, x_404);
x_406 = l_Lean_Elab_Term_expandShow___closed__2;
x_407 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_407, 0, x_386);
lean_ctor_set(x_407, 1, x_406);
x_408 = lean_array_push(x_390, x_407);
x_409 = lean_array_push(x_408, x_338);
x_410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_410, 0, x_334);
lean_ctor_set(x_410, 1, x_409);
x_411 = lean_array_push(x_405, x_410);
x_412 = l_Lean_Parser_Term_have___elambda__1___closed__1;
x_413 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_411);
x_414 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_387);
return x_414;
}
}
}
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
lean_dec(x_344);
x_415 = lean_unsigned_to_nat(5u);
x_416 = l_Lean_Syntax_getArg(x_1, x_415);
lean_dec(x_1);
x_417 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_418 = !lean_is_exclusive(x_417);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_419 = lean_ctor_get(x_417, 0);
x_420 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_419);
x_421 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
x_422 = l_Array_empty___closed__1;
x_423 = lean_array_push(x_422, x_421);
x_424 = l_Lean_Elab_Term_expandHave___closed__2;
x_425 = lean_array_push(x_423, x_424);
x_426 = lean_array_push(x_425, x_329);
x_427 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_419);
x_428 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_428, 0, x_419);
lean_ctor_set(x_428, 1, x_427);
x_429 = lean_array_push(x_422, x_428);
x_430 = lean_array_push(x_429, x_416);
x_431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_431, 0, x_332);
lean_ctor_set(x_431, 1, x_430);
x_432 = lean_array_push(x_426, x_431);
x_433 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
lean_inc(x_419);
x_434 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_434, 0, x_419);
lean_ctor_set(x_434, 1, x_433);
x_435 = lean_array_push(x_422, x_434);
x_436 = l_Lean_nullKind___closed__2;
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_435);
x_438 = lean_array_push(x_432, x_437);
x_439 = l_Lean_Elab_Term_expandShow___closed__2;
x_440 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_440, 0, x_419);
lean_ctor_set(x_440, 1, x_439);
x_441 = lean_array_push(x_422, x_440);
x_442 = lean_array_push(x_441, x_338);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_334);
lean_ctor_set(x_443, 1, x_442);
x_444 = lean_array_push(x_438, x_443);
x_445 = l_Lean_Parser_Term_have___elambda__1___closed__1;
x_446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_444);
lean_ctor_set(x_417, 0, x_446);
return x_417;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_447 = lean_ctor_get(x_417, 0);
x_448 = lean_ctor_get(x_417, 1);
lean_inc(x_448);
lean_inc(x_447);
lean_dec(x_417);
x_449 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_447);
x_450 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_450, 0, x_447);
lean_ctor_set(x_450, 1, x_449);
x_451 = l_Array_empty___closed__1;
x_452 = lean_array_push(x_451, x_450);
x_453 = l_Lean_Elab_Term_expandHave___closed__2;
x_454 = lean_array_push(x_452, x_453);
x_455 = lean_array_push(x_454, x_329);
x_456 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_447);
x_457 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_457, 0, x_447);
lean_ctor_set(x_457, 1, x_456);
x_458 = lean_array_push(x_451, x_457);
x_459 = lean_array_push(x_458, x_416);
x_460 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_460, 0, x_332);
lean_ctor_set(x_460, 1, x_459);
x_461 = lean_array_push(x_455, x_460);
x_462 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
lean_inc(x_447);
x_463 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_463, 0, x_447);
lean_ctor_set(x_463, 1, x_462);
x_464 = lean_array_push(x_451, x_463);
x_465 = l_Lean_nullKind___closed__2;
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_464);
x_467 = lean_array_push(x_461, x_466);
x_468 = l_Lean_Elab_Term_expandShow___closed__2;
x_469 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_469, 0, x_447);
lean_ctor_set(x_469, 1, x_468);
x_470 = lean_array_push(x_451, x_469);
x_471 = lean_array_push(x_470, x_338);
x_472 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_472, 0, x_334);
lean_ctor_set(x_472, 1, x_471);
x_473 = lean_array_push(x_467, x_472);
x_474 = l_Lean_Parser_Term_have___elambda__1___closed__1;
x_475 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_475, 0, x_474);
lean_ctor_set(x_475, 1, x_473);
x_476 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_476, 0, x_475);
lean_ctor_set(x_476, 1, x_448);
return x_476;
}
}
}
}
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; 
x_477 = l_Lean_Syntax_getArg(x_331, x_8);
lean_dec(x_331);
x_478 = lean_unsigned_to_nat(4u);
x_479 = l_Lean_Syntax_getArg(x_1, x_478);
x_480 = l_Lean_Syntax_isNone(x_479);
if (x_480 == 0)
{
lean_object* x_481; uint8_t x_482; 
x_481 = l_Lean_nullKind___closed__2;
lean_inc(x_479);
x_482 = l_Lean_Syntax_isOfKind(x_479, x_481);
if (x_482 == 0)
{
lean_object* x_483; lean_object* x_484; 
lean_dec(x_479);
lean_dec(x_477);
lean_dec(x_329);
lean_dec(x_1);
x_483 = lean_box(1);
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_3);
return x_484;
}
else
{
lean_object* x_485; lean_object* x_486; uint8_t x_487; 
x_485 = l_Lean_Syntax_getArgs(x_479);
lean_dec(x_479);
x_486 = lean_array_get_size(x_485);
lean_dec(x_485);
x_487 = lean_nat_dec_eq(x_486, x_8);
lean_dec(x_486);
if (x_487 == 0)
{
lean_object* x_488; lean_object* x_489; 
lean_dec(x_477);
lean_dec(x_329);
lean_dec(x_1);
x_488 = lean_box(1);
x_489 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_3);
return x_489;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; uint8_t x_493; 
x_490 = lean_unsigned_to_nat(5u);
x_491 = l_Lean_Syntax_getArg(x_1, x_490);
lean_dec(x_1);
x_492 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_493 = !lean_is_exclusive(x_492);
if (x_493 == 0)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_494 = lean_ctor_get(x_492, 0);
x_495 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_494);
x_496 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_496, 0, x_494);
lean_ctor_set(x_496, 1, x_495);
x_497 = l_Array_empty___closed__1;
x_498 = lean_array_push(x_497, x_496);
x_499 = l_Lean_Elab_Term_expandHave___closed__2;
x_500 = lean_array_push(x_498, x_499);
x_501 = lean_array_push(x_500, x_329);
x_502 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_494);
x_503 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_503, 0, x_494);
lean_ctor_set(x_503, 1, x_502);
x_504 = lean_array_push(x_497, x_503);
x_505 = lean_array_push(x_504, x_491);
x_506 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_506, 0, x_332);
lean_ctor_set(x_506, 1, x_505);
x_507 = lean_array_push(x_501, x_506);
x_508 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_509 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_509, 0, x_494);
lean_ctor_set(x_509, 1, x_508);
x_510 = lean_array_push(x_497, x_509);
x_511 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_511, 0, x_481);
lean_ctor_set(x_511, 1, x_510);
x_512 = lean_array_push(x_507, x_511);
x_513 = lean_array_push(x_512, x_477);
x_514 = l_Lean_Parser_Term_have___elambda__1___closed__1;
x_515 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_515, 0, x_514);
lean_ctor_set(x_515, 1, x_513);
lean_ctor_set(x_492, 0, x_515);
return x_492;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_516 = lean_ctor_get(x_492, 0);
x_517 = lean_ctor_get(x_492, 1);
lean_inc(x_517);
lean_inc(x_516);
lean_dec(x_492);
x_518 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_516);
x_519 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_519, 0, x_516);
lean_ctor_set(x_519, 1, x_518);
x_520 = l_Array_empty___closed__1;
x_521 = lean_array_push(x_520, x_519);
x_522 = l_Lean_Elab_Term_expandHave___closed__2;
x_523 = lean_array_push(x_521, x_522);
x_524 = lean_array_push(x_523, x_329);
x_525 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_516);
x_526 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_526, 0, x_516);
lean_ctor_set(x_526, 1, x_525);
x_527 = lean_array_push(x_520, x_526);
x_528 = lean_array_push(x_527, x_491);
x_529 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_529, 0, x_332);
lean_ctor_set(x_529, 1, x_528);
x_530 = lean_array_push(x_524, x_529);
x_531 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_532 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_532, 0, x_516);
lean_ctor_set(x_532, 1, x_531);
x_533 = lean_array_push(x_520, x_532);
x_534 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_534, 0, x_481);
lean_ctor_set(x_534, 1, x_533);
x_535 = lean_array_push(x_530, x_534);
x_536 = lean_array_push(x_535, x_477);
x_537 = l_Lean_Parser_Term_have___elambda__1___closed__1;
x_538 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_538, 0, x_537);
lean_ctor_set(x_538, 1, x_536);
x_539 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_539, 0, x_538);
lean_ctor_set(x_539, 1, x_517);
return x_539;
}
}
}
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; uint8_t x_543; 
lean_dec(x_479);
x_540 = lean_unsigned_to_nat(5u);
x_541 = l_Lean_Syntax_getArg(x_1, x_540);
lean_dec(x_1);
x_542 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_543 = !lean_is_exclusive(x_542);
if (x_543 == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_544 = lean_ctor_get(x_542, 0);
x_545 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_544);
x_546 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_546, 0, x_544);
lean_ctor_set(x_546, 1, x_545);
x_547 = l_Array_empty___closed__1;
x_548 = lean_array_push(x_547, x_546);
x_549 = l_Lean_Elab_Term_expandHave___closed__2;
x_550 = lean_array_push(x_548, x_549);
x_551 = lean_array_push(x_550, x_329);
x_552 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_544);
x_553 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_553, 0, x_544);
lean_ctor_set(x_553, 1, x_552);
x_554 = lean_array_push(x_547, x_553);
x_555 = lean_array_push(x_554, x_541);
x_556 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_556, 0, x_332);
lean_ctor_set(x_556, 1, x_555);
x_557 = lean_array_push(x_551, x_556);
x_558 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_559 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_559, 0, x_544);
lean_ctor_set(x_559, 1, x_558);
x_560 = lean_array_push(x_547, x_559);
x_561 = l_Lean_nullKind___closed__2;
x_562 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_562, 0, x_561);
lean_ctor_set(x_562, 1, x_560);
x_563 = lean_array_push(x_557, x_562);
x_564 = lean_array_push(x_563, x_477);
x_565 = l_Lean_Parser_Term_have___elambda__1___closed__1;
x_566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_564);
lean_ctor_set(x_542, 0, x_566);
return x_542;
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_567 = lean_ctor_get(x_542, 0);
x_568 = lean_ctor_get(x_542, 1);
lean_inc(x_568);
lean_inc(x_567);
lean_dec(x_542);
x_569 = l_Lean_Parser_Tactic_have___closed__1;
lean_inc(x_567);
x_570 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_570, 0, x_567);
lean_ctor_set(x_570, 1, x_569);
x_571 = l_Array_empty___closed__1;
x_572 = lean_array_push(x_571, x_570);
x_573 = l_Lean_Elab_Term_expandHave___closed__2;
x_574 = lean_array_push(x_572, x_573);
x_575 = lean_array_push(x_574, x_329);
x_576 = l_Lean_Elab_Term_expandShow___closed__1;
lean_inc(x_567);
x_577 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_577, 0, x_567);
lean_ctor_set(x_577, 1, x_576);
x_578 = lean_array_push(x_571, x_577);
x_579 = lean_array_push(x_578, x_541);
x_580 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_580, 0, x_332);
lean_ctor_set(x_580, 1, x_579);
x_581 = lean_array_push(x_575, x_580);
x_582 = l_myMacro____x40_Init_Notation___hyg_13394____closed__12;
x_583 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_583, 0, x_567);
lean_ctor_set(x_583, 1, x_582);
x_584 = lean_array_push(x_571, x_583);
x_585 = l_Lean_nullKind___closed__2;
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_585);
lean_ctor_set(x_586, 1, x_584);
x_587 = lean_array_push(x_581, x_586);
x_588 = lean_array_push(x_587, x_477);
x_589 = l_Lean_Parser_Term_have___elambda__1___closed__1;
x_590 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_588);
x_591 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_568);
return x_591;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_expandSuffices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandSuffices(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandSuffices___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSuffices___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandSuffices(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_Lean_Parser_Term_suffices___elambda__1___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandSuffices___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get_usize(x_4, 2);
lean_dec(x_4);
x_11 = lean_box_usize(x_10);
x_12 = lean_apply_6(x_2, x_8, x_9, x_11, x_7, x_5, x_6);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_apply_1(x_3, x_1);
return x_13;
}
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__2___rarg), 3, 0);
return x_2;
}
}
uint8_t l_List_beq___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_nat_dec_eq(x_6, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid `parser!` macro, it must be used in definitions");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid `parser!` macro, unexpected declaration name");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Parser.leadingNode");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__7;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__8;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("leadingNode");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__4;
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("OrElse.orElse");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__15;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("OrElse");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("orElse");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__18;
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Parser.mkAntiquot");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__24;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkAntiquot");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__4;
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__26;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__28;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprOption___rarg___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_instReprOption___rarg___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__30;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_instReprOption___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__33;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__5;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__35;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__38;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_getDeclName_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__3;
x_14 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
lean_inc(x_16);
x_17 = l_Lean_extractMacroScopes(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_19 = lean_ctor_get(x_17, 3);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Init_Meta_0__Lean_quoteName(x_16);
x_22 = l_Lean_instInhabitedSourceInfo___closed__1;
x_23 = l_Lean_Syntax_mkStrLit(x_20, x_22);
lean_dec(x_20);
x_24 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_7, x_8, x_15);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__11;
x_33 = l_Lean_addMacroScope(x_30, x_32, x_27);
x_34 = lean_box(0);
x_35 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__9;
x_36 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__13;
x_37 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_37, 0, x_22);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_33);
lean_ctor_set(x_37, 3, x_36);
x_38 = l_Array_empty___closed__1;
x_39 = lean_array_push(x_38, x_37);
x_40 = lean_array_push(x_38, x_21);
lean_inc(x_40);
x_41 = lean_array_push(x_40, x_1);
x_42 = lean_array_push(x_41, x_2);
x_43 = l_Lean_nullKind___closed__2;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_array_push(x_39, x_44);
x_46 = l_myMacro____x40_Init_Notation___hyg_1989____closed__4;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_List_beq___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___spec__1(x_19, x_34);
lean_dec(x_19);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_40);
x_49 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_7, x_8, x_31);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_51);
lean_dec(x_3);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_54);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20;
lean_inc(x_53);
lean_inc(x_57);
x_59 = l_Lean_addMacroScope(x_57, x_58, x_53);
x_60 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16;
x_61 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22;
x_62 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_62, 0, x_22);
lean_ctor_set(x_62, 1, x_60);
lean_ctor_set(x_62, 2, x_59);
lean_ctor_set(x_62, 3, x_61);
x_63 = lean_array_push(x_38, x_62);
x_64 = l_prec_x28___x29___closed__3;
lean_inc(x_50);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_50);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_array_push(x_38, x_65);
x_67 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27;
lean_inc(x_53);
lean_inc(x_57);
x_68 = l_Lean_addMacroScope(x_57, x_67, x_53);
x_69 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25;
x_70 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29;
x_71 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_71, 0, x_22);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_68);
lean_ctor_set(x_71, 3, x_70);
x_72 = lean_array_push(x_38, x_71);
x_73 = lean_array_push(x_38, x_23);
x_74 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__32;
x_75 = l_Lean_addMacroScope(x_57, x_74, x_53);
x_76 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__31;
x_77 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__34;
x_78 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_78, 0, x_22);
lean_ctor_set(x_78, 1, x_76);
lean_ctor_set(x_78, 2, x_75);
lean_ctor_set(x_78, 3, x_77);
x_79 = lean_array_push(x_73, x_78);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_43);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_array_push(x_72, x_80);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_46);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_array_push(x_38, x_82);
x_84 = l_myMacro____x40_Init_Notation___hyg_1192____closed__8;
x_85 = lean_array_push(x_83, x_84);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_43);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_array_push(x_66, x_86);
x_88 = l_prec_x28___x29___closed__7;
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_50);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_array_push(x_87, x_89);
x_91 = l_myMacro____x40_Init_Notation___hyg_11370____closed__8;
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = lean_array_push(x_38, x_92);
x_94 = lean_array_push(x_93, x_47);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_43);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_array_push(x_63, x_95);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_46);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_55, 0, x_97);
return x_55;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_98 = lean_ctor_get(x_55, 0);
x_99 = lean_ctor_get(x_55, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_55);
x_100 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20;
lean_inc(x_53);
lean_inc(x_98);
x_101 = l_Lean_addMacroScope(x_98, x_100, x_53);
x_102 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16;
x_103 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22;
x_104 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_104, 0, x_22);
lean_ctor_set(x_104, 1, x_102);
lean_ctor_set(x_104, 2, x_101);
lean_ctor_set(x_104, 3, x_103);
x_105 = lean_array_push(x_38, x_104);
x_106 = l_prec_x28___x29___closed__3;
lean_inc(x_50);
x_107 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_107, 0, x_50);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_array_push(x_38, x_107);
x_109 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27;
lean_inc(x_53);
lean_inc(x_98);
x_110 = l_Lean_addMacroScope(x_98, x_109, x_53);
x_111 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25;
x_112 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29;
x_113 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_113, 0, x_22);
lean_ctor_set(x_113, 1, x_111);
lean_ctor_set(x_113, 2, x_110);
lean_ctor_set(x_113, 3, x_112);
x_114 = lean_array_push(x_38, x_113);
x_115 = lean_array_push(x_38, x_23);
x_116 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__32;
x_117 = l_Lean_addMacroScope(x_98, x_116, x_53);
x_118 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__31;
x_119 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__34;
x_120 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_120, 0, x_22);
lean_ctor_set(x_120, 1, x_118);
lean_ctor_set(x_120, 2, x_117);
lean_ctor_set(x_120, 3, x_119);
x_121 = lean_array_push(x_115, x_120);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_43);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_array_push(x_114, x_122);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_46);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_array_push(x_38, x_124);
x_126 = l_myMacro____x40_Init_Notation___hyg_1192____closed__8;
x_127 = lean_array_push(x_125, x_126);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_43);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_array_push(x_108, x_128);
x_130 = l_prec_x28___x29___closed__7;
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_50);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_array_push(x_129, x_131);
x_133 = l_myMacro____x40_Init_Notation___hyg_11370____closed__8;
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
x_135 = lean_array_push(x_38, x_134);
x_136 = lean_array_push(x_135, x_47);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_43);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_array_push(x_105, x_137);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_46);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_99);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_141 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_7, x_8, x_31);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_143);
lean_dec(x_3);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_146);
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_149 = lean_ctor_get(x_147, 0);
x_150 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20;
lean_inc(x_145);
lean_inc(x_149);
x_151 = l_Lean_addMacroScope(x_149, x_150, x_145);
x_152 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16;
x_153 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22;
x_154 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_154, 0, x_22);
lean_ctor_set(x_154, 1, x_152);
lean_ctor_set(x_154, 2, x_151);
lean_ctor_set(x_154, 3, x_153);
x_155 = lean_array_push(x_38, x_154);
x_156 = l_prec_x28___x29___closed__3;
lean_inc(x_142);
x_157 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_157, 0, x_142);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_array_push(x_38, x_157);
x_159 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27;
lean_inc(x_145);
lean_inc(x_149);
x_160 = l_Lean_addMacroScope(x_149, x_159, x_145);
x_161 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25;
x_162 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29;
x_163 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_163, 0, x_22);
lean_ctor_set(x_163, 1, x_161);
lean_ctor_set(x_163, 2, x_160);
lean_ctor_set(x_163, 3, x_162);
x_164 = lean_array_push(x_38, x_163);
x_165 = lean_array_push(x_38, x_23);
x_166 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__37;
x_167 = l_Lean_addMacroScope(x_149, x_166, x_145);
x_168 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__36;
x_169 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__39;
x_170 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_170, 0, x_22);
lean_ctor_set(x_170, 1, x_168);
lean_ctor_set(x_170, 2, x_167);
lean_ctor_set(x_170, 3, x_169);
x_171 = lean_array_push(x_38, x_170);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_43);
lean_ctor_set(x_172, 1, x_40);
x_173 = lean_array_push(x_171, x_172);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_46);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_array_push(x_38, x_174);
x_176 = l_myMacro____x40_Init_Notation___hyg_1192____closed__8;
x_177 = lean_array_push(x_175, x_176);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_43);
lean_ctor_set(x_178, 1, x_177);
lean_inc(x_158);
x_179 = lean_array_push(x_158, x_178);
x_180 = l_prec_x28___x29___closed__7;
x_181 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_181, 0, x_142);
lean_ctor_set(x_181, 1, x_180);
lean_inc(x_181);
x_182 = lean_array_push(x_179, x_181);
x_183 = l_myMacro____x40_Init_Notation___hyg_11370____closed__8;
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
x_185 = lean_array_push(x_165, x_184);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_43);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_array_push(x_164, x_186);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_46);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_array_push(x_38, x_188);
x_190 = lean_array_push(x_189, x_176);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_43);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_array_push(x_158, x_191);
x_193 = lean_array_push(x_192, x_181);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_183);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_array_push(x_38, x_194);
x_196 = lean_array_push(x_195, x_47);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_43);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_array_push(x_155, x_197);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_46);
lean_ctor_set(x_199, 1, x_198);
lean_ctor_set(x_147, 0, x_199);
return x_147;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_200 = lean_ctor_get(x_147, 0);
x_201 = lean_ctor_get(x_147, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_147);
x_202 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20;
lean_inc(x_145);
lean_inc(x_200);
x_203 = l_Lean_addMacroScope(x_200, x_202, x_145);
x_204 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16;
x_205 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22;
x_206 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_206, 0, x_22);
lean_ctor_set(x_206, 1, x_204);
lean_ctor_set(x_206, 2, x_203);
lean_ctor_set(x_206, 3, x_205);
x_207 = lean_array_push(x_38, x_206);
x_208 = l_prec_x28___x29___closed__3;
lean_inc(x_142);
x_209 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_209, 0, x_142);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_array_push(x_38, x_209);
x_211 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27;
lean_inc(x_145);
lean_inc(x_200);
x_212 = l_Lean_addMacroScope(x_200, x_211, x_145);
x_213 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25;
x_214 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29;
x_215 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_215, 0, x_22);
lean_ctor_set(x_215, 1, x_213);
lean_ctor_set(x_215, 2, x_212);
lean_ctor_set(x_215, 3, x_214);
x_216 = lean_array_push(x_38, x_215);
x_217 = lean_array_push(x_38, x_23);
x_218 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__37;
x_219 = l_Lean_addMacroScope(x_200, x_218, x_145);
x_220 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__36;
x_221 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__39;
x_222 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_222, 0, x_22);
lean_ctor_set(x_222, 1, x_220);
lean_ctor_set(x_222, 2, x_219);
lean_ctor_set(x_222, 3, x_221);
x_223 = lean_array_push(x_38, x_222);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_43);
lean_ctor_set(x_224, 1, x_40);
x_225 = lean_array_push(x_223, x_224);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_46);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_array_push(x_38, x_226);
x_228 = l_myMacro____x40_Init_Notation___hyg_1192____closed__8;
x_229 = lean_array_push(x_227, x_228);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_43);
lean_ctor_set(x_230, 1, x_229);
lean_inc(x_210);
x_231 = lean_array_push(x_210, x_230);
x_232 = l_prec_x28___x29___closed__7;
x_233 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_233, 0, x_142);
lean_ctor_set(x_233, 1, x_232);
lean_inc(x_233);
x_234 = lean_array_push(x_231, x_233);
x_235 = l_myMacro____x40_Init_Notation___hyg_11370____closed__8;
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_234);
x_237 = lean_array_push(x_217, x_236);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_43);
lean_ctor_set(x_238, 1, x_237);
x_239 = lean_array_push(x_216, x_238);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_46);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_array_push(x_38, x_240);
x_242 = lean_array_push(x_241, x_228);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_43);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_array_push(x_210, x_243);
x_245 = lean_array_push(x_244, x_233);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_235);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_array_push(x_38, x_246);
x_248 = lean_array_push(x_247, x_47);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_43);
lean_ctor_set(x_249, 1, x_248);
x_250 = lean_array_push(x_207, x_249);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_46);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_201);
return x_252;
}
}
}
else
{
lean_object* x_253; lean_object* x_254; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_253 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__6;
x_254 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_253, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_254;
}
}
}
}
lean_object* l_List_beq___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_maxPrec;
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_numLitKind;
x_2 = l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__1;
x_3 = l_Lean_instInhabitedSourceInfo___closed__1;
x_4 = l_Lean_Syntax_mkLit(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabParserMacro___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Parser_Term_parser_x21___elambda__1___closed__2;
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3___rarg(x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_27; uint8_t x_28; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_27 = l_Lean_nullKind___closed__2;
lean_inc(x_13);
x_28 = l_Lean_Syntax_isOfKind(x_13, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_box(0);
x_14 = x_29;
goto block_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = l_Lean_Syntax_getArgs(x_13);
x_31 = lean_array_get_size(x_30);
lean_dec(x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_eq(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_box(0);
x_14 = x_34;
goto block_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_13);
x_35 = lean_unsigned_to_nat(2u);
x_36 = l_Lean_Syntax_getArg(x_1, x_35);
lean_dec(x_1);
x_37 = l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__2;
x_38 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux(x_37, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_38;
}
}
block_26:
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_14);
x_15 = l_Lean_nullKind___closed__2;
lean_inc(x_13);
x_16 = l_Lean_Syntax_isOfKind(x_13, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3___rarg(x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = l_Lean_Syntax_getArgs(x_13);
x_19 = lean_array_get_size(x_18);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3___rarg(x_8);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_24 = l_Lean_Syntax_getArg(x_1, x_20);
lean_dec(x_1);
x_25 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux(x_23, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_25;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabParserMacro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabParserMacro___lambda__1___boxed), 8, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_elabParserMacro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_elabParserMacro___closed__1;
x_11 = l_Lean_Elab_Term_adaptExpander(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabParserMacro___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabParserMacro___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabParserMacro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabParserMacro), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabParserMacro(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_parser_x21___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabParserMacro___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid `tparser!` macro, it must be used in definitions");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Parser.trailingNode");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__4;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trailingNode");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__4;
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_getDeclName_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__3;
x_14 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l___private_Init_Meta_0__Lean_quoteName(x_16);
x_18 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_7, x_8, x_15);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__8;
x_27 = l_Lean_addMacroScope(x_25, x_26, x_21);
x_28 = l_Lean_instInhabitedSourceInfo___closed__1;
x_29 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__6;
x_30 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__10;
x_31 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set(x_31, 3, x_30);
x_32 = l_Array_empty___closed__1;
x_33 = lean_array_push(x_32, x_31);
x_34 = lean_array_push(x_32, x_17);
x_35 = lean_array_push(x_34, x_1);
x_36 = lean_array_push(x_35, x_2);
x_37 = l_Lean_nullKind___closed__2;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_array_push(x_33, x_38);
x_40 = l_myMacro____x40_Init_Notation___hyg_1989____closed__4;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_23, 0, x_41);
return x_23;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_42 = lean_ctor_get(x_23, 0);
x_43 = lean_ctor_get(x_23, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_23);
x_44 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__8;
x_45 = l_Lean_addMacroScope(x_42, x_44, x_21);
x_46 = l_Lean_instInhabitedSourceInfo___closed__1;
x_47 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__6;
x_48 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__10;
x_49 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_45);
lean_ctor_set(x_49, 3, x_48);
x_50 = l_Array_empty___closed__1;
x_51 = lean_array_push(x_50, x_49);
x_52 = lean_array_push(x_50, x_17);
x_53 = lean_array_push(x_52, x_1);
x_54 = lean_array_push(x_53, x_2);
x_55 = l_Lean_nullKind___closed__2;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_array_push(x_51, x_56);
x_58 = l_myMacro____x40_Init_Notation___hyg_1989____closed__4;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_43);
return x_60;
}
}
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_elabTParserMacro___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Parser_Term_tparser_x21___elambda__1___closed__2;
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3___rarg(x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_27; uint8_t x_28; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_27 = l_Lean_nullKind___closed__2;
lean_inc(x_13);
x_28 = l_Lean_Syntax_isOfKind(x_13, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_box(0);
x_14 = x_29;
goto block_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = l_Lean_Syntax_getArgs(x_13);
x_31 = lean_array_get_size(x_30);
lean_dec(x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_eq(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_box(0);
x_14 = x_34;
goto block_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_13);
x_35 = lean_unsigned_to_nat(2u);
x_36 = l_Lean_Syntax_getArg(x_1, x_35);
lean_dec(x_1);
x_37 = l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__2;
x_38 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(x_37, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_38;
}
}
block_26:
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_14);
x_15 = l_Lean_nullKind___closed__2;
lean_inc(x_13);
x_16 = l_Lean_Syntax_isOfKind(x_13, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3___rarg(x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = l_Lean_Syntax_getArgs(x_13);
x_19 = lean_array_get_size(x_18);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3___rarg(x_8);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_24 = l_Lean_Syntax_getArg(x_1, x_20);
lean_dec(x_1);
x_25 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(x_23, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_25;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabTParserMacro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTParserMacro___lambda__1___boxed), 8, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_elabTParserMacro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_elabTParserMacro___closed__1;
x_11 = l_Lean_Elab_Term_adaptExpander(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabTParserMacro___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabTParserMacro___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTParserMacro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTParserMacro), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabTParserMacro(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_tparser_x21___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabTParserMacro___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_nativeRefl");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__2;
lean_inc(x_3);
x_11 = l_Lean_Elab_Term_mkAuxName(x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
lean_inc(x_12);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_1);
x_16 = lean_box(1);
x_17 = 0;
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_7);
lean_inc(x_3);
x_20 = l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_compileDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__4(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
lean_dec(x_19);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_12);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_12);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
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
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_11);
if (x_35 == 0)
{
return x_11;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_11, 0);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_11);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid macro application, term contains free variables");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasFVar(x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = l_Lean_indentExpr(x_1);
x_13 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__2;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_KernelException_toMessageData___closed__15;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at_Lean_Elab_Term_elabLetDeclAux___spec__1(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid macro application, term contains metavariables");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Elab_Term_elabTermAndSynthesize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_hasMVar(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1(x_11, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = l_Lean_indentExpr(x_11);
x_17 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_KernelException_toMessageData___closed__15;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_elabNativeRefl_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabNativeRefl_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNativeRefl_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabNativeRefl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_Meta_mkEqRefl___at_Lean_Elab_Term_elabNativeRefl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_mkEq___at_Lean_Elab_Term_elabNativeRefl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Meta_mkExpectedTypeHint___at_Lean_Elab_Term_elabNativeRefl___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkExpectedTypeHintImp(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to reduce term at `nativeRefl!` macro application");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_reduceNative_x3f___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ofReduceNat");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__2;
x_2 = l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_reduceNative_x3f___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ofReduceBool");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__2;
x_2 = l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_instQuoteBool___closed__2;
x_15 = l_Lean_Expr_isConstOf(x_1, x_14);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = l_Lean_mkConst(x_12, x_16);
if (x_15 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__3;
lean_inc(x_17);
x_47 = l_Lean_mkApp(x_46, x_17);
x_48 = l_Lean_Meta_reduceNative_x3f(x_47, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__5;
x_18 = x_51;
x_19 = x_49;
x_20 = x_50;
goto block_45;
}
else
{
uint8_t x_52; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
return x_48;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_48, 0);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_48);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__6;
lean_inc(x_17);
x_57 = l_Lean_mkApp(x_56, x_17);
x_58 = l_Lean_Meta_reduceNative_x3f(x_57, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__8;
x_18 = x_61;
x_19 = x_59;
x_20 = x_60;
goto block_45;
}
else
{
uint8_t x_62; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
return x_58;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_58, 0);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_58);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
block_45:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_18);
lean_dec(x_17);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_2);
x_22 = l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_KernelException_toMessageData___closed__15;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at_Lean_Elab_Term_elabNativeRefl___spec__1(x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_4);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_27);
x_28 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(x_27, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_mkConst(x_18, x_16);
lean_inc(x_27);
x_32 = l_Lean_mkApp3(x_31, x_17, x_27, x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_33 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_2, x_27, x_6, x_7, x_8, x_9, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkExpectedTypeHintImp(x_32, x_34, x_6, x_7, x_8, x_9, x_35);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_28, 0);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_28);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_11);
if (x_66 == 0)
{
return x_11;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_11, 0);
x_68 = lean_ctor_get(x_11, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_11);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid `nativeRefl!` macro application, term must have type `Nat` or `Bool`");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeRefl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabNativeRefl___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabNativeRefl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_16 = l_Lean_Meta_inferType(x_14, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_Lean_Meta_whnf(x_17, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_instQuoteBool___closed__2;
x_23 = l_Lean_Expr_isConstOf(x_20, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Literal_type___closed__2;
x_25 = l_Lean_Expr_isConstOf(x_20, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_14);
x_26 = l_Lean_indentExpr(x_20);
x_27 = l_Lean_Elab_Term_elabNativeRefl___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_KernelException_toMessageData___closed__15;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(0);
x_37 = l_Lean_Elab_Term_elabNativeRefl___lambda__1(x_20, x_14, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
lean_dec(x_4);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
x_39 = l_Lean_Elab_Term_elabNativeRefl___lambda__1(x_20, x_14, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
lean_dec(x_4);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_19);
if (x_40 == 0)
{
return x_19;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_19, 0);
x_42 = lean_ctor_get(x_19, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_19);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_16);
if (x_44 == 0)
{
return x_16;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_16, 0);
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_16);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_13);
if (x_48 == 0)
{
return x_13;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_13, 0);
x_50 = lean_ctor_get(x_13, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_13);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabNativeRefl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Term_elabNativeRefl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Meta_mkEqRefl___at_Lean_Elab_Term_elabNativeRefl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkEqRefl___at_Lean_Elab_Term_elabNativeRefl___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_mkEq___at_Lean_Elab_Term_elabNativeRefl___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkEq___at_Lean_Elab_Term_elabNativeRefl___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Meta_mkExpectedTypeHint___at_Lean_Elab_Term_elabNativeRefl___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkExpectedTypeHint___at_Lean_Elab_Term_elabNativeRefl___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_elabNativeRefl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabNativeRefl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabNativeRefl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabNativeRefl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNativeRefl___boxed), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabNativeRefl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_nativeRefl___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid macro, expected type is not available");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected type must not contain free or meta variables");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__3;
x_12 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = 1;
x_16 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Meta_instantiateMVars(x_14, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = l_Lean_Expr_hasFVar(x_21);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Expr_hasMVar(x_21);
if (x_24 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_free_object(x_19);
x_25 = l_Lean_indentExpr(x_21);
x_26 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__5;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_KernelException_toMessageData___closed__15;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_free_object(x_19);
x_35 = l_Lean_indentExpr(x_21);
x_36 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__5;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_KernelException_toMessageData___closed__15;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_19, 0);
x_46 = lean_ctor_get(x_19, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_19);
x_47 = l_Lean_Expr_hasFVar(x_45);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Expr_hasMVar(x_45);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = l_Lean_indentExpr(x_45);
x_51 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__5;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_KernelException_toMessageData___closed__15;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = l_Lean_indentExpr(x_45);
x_61 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__5;
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Lean_KernelException_toMessageData___closed__15;
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_64, x_2, x_3, x_4, x_5, x_6, x_7, x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_19);
if (x_70 == 0)
{
return x_19;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_19, 0);
x_72 = lean_ctor_get(x_19, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_19);
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
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_17);
if (x_74 == 0)
{
return x_17;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_17, 0);
x_76 = lean_ctor_get(x_17, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_17);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_9);
if (x_78 == 0)
{
return x_9;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_9, 0);
x_80 = lean_ctor_get(x_9, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_9);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
lean_object* l_Lean_Meta_mkDecide___at_Lean_Elab_Term_elabNativeDecide___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = lean_box(0);
x_11 = l_Lean_Syntax_mkApp___closed__1;
x_12 = lean_array_push(x_11, x_9);
x_13 = lean_array_push(x_12, x_10);
x_14 = l_Lean_Meta_mkDecide___rarg___closed__1;
x_15 = l_Lean_Meta_mkAppOptM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryPureCoe_x3f___spec__2(x_14, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
}
lean_object* l_Lean_Meta_mkEqRefl___at_Lean_Elab_Term_elabNativeDecide___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_mkExpectedTypeHint___at_Lean_Elab_Term_elabNativeDecide___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkExpectedTypeHintImp(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabNativeDecide___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__8;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabNativeDecide___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_12 = l_Lean_Meta_mkDecide___at_Lean_Elab_Term_elabNativeDecide___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_Lean_instToExprBool___closed__1;
lean_inc(x_6);
x_17 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl(x_16, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_3);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_mkSorry___rarg___lambda__1___closed__4;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(x_20, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_mkConst(x_18, x_15);
x_25 = l_Lean_Elab_Term_elabNativeDecide___rarg___closed__1;
x_26 = l_Lean_mkApp3(x_25, x_24, x_20, x_22);
x_27 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkExpectedTypeHintImp(x_26, x_10, x_4, x_5, x_6, x_7, x_23);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_12);
if (x_36 == 0)
{
return x_12;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_12);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
return x_9;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_9, 0);
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_9);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabNativeDecide(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNativeDecide___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkDecide___at_Lean_Elab_Term_elabNativeDecide___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkDecide___at_Lean_Elab_Term_elabNativeDecide___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_mkEqRefl___at_Lean_Elab_Term_elabNativeDecide___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkEqRefl___at_Lean_Elab_Term_elabNativeDecide___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_mkExpectedTypeHint___at_Lean_Elab_Term_elabNativeDecide___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkExpectedTypeHint___at_Lean_Elab_Term_elabNativeDecide___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_elabNativeDecide___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_elabNativeDecide(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNativeDecide___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabNativeDecide(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_nativeDecide___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabDecide___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabDecide___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_12 = l_Lean_Meta_mkDecide___at_Lean_Elab_Term_elabNativeDecide___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Meta_instantiateMVars(x_13, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_appArg_x21(x_16);
lean_dec(x_16);
x_19 = l_Lean_instToExprBool___lambda__1___closed__2;
x_20 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(x_19, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Lean_Elab_Term_elabDecide___rarg___closed__1;
x_24 = l_Lean_mkApp3(x_23, x_10, x_18, x_22);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = l_Lean_Elab_Term_elabDecide___rarg___closed__1;
x_28 = l_Lean_mkApp3(x_27, x_10, x_18, x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_18);
lean_dec(x_10);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
return x_15;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
return x_12;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_12, 0);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_12);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l_Lean_Elab_Term_elabDecide(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDecide___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabDecide___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_elabDecide(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabDecide___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDecide___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabDecide(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_14860____closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabDecide___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabPanic_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_elabPanic_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabPanic_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = l_Lean_Syntax_getPos(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg___boxed), 3, 0);
return x_5;
}
}
lean_object* l_Lean_Elab_getRefPosition___at_Lean_Elab_Term_elabPanic___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg(x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_FileMap_toPosition(x_8, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = l_Lean_FileMap_toPosition(x_8, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
lean_object* l_Lean_Elab_Term_elabPanic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 3);
lean_inc(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_4, 3, x_14);
x_15 = 1;
x_16 = l_Lean_Elab_Term_elabTerm(x_3, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_ctor_get(x_4, 3);
x_21 = lean_ctor_get(x_4, 4);
x_22 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_23 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_24 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 2);
x_25 = lean_ctor_get(x_4, 5);
lean_inc(x_25);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
lean_inc(x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_3);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
x_28 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_28, 2, x_19);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_28, 4, x_21);
lean_ctor_set(x_28, 5, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*6, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*6 + 1, x_23);
lean_ctor_set_uint8(x_28, sizeof(void*)*6 + 2, x_24);
x_29 = 1;
x_30 = l_Lean_Elab_Term_elabTerm(x_3, x_2, x_29, x_28, x_5, x_6, x_7, x_8, x_9, x_10);
return x_30;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("panicWithPos");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabPanic___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_elabPanic___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_elabPanic___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabPanic___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabPanic___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabPanic___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("panicWithPosWithDecl");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabPanic___closed__7;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_elabPanic___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_elabPanic___closed__8;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabPanic___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabPanic___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabPanic___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabPanic___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabPanic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Elab_getRefPosition___at_Lean_Elab_Term_elabPanic___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_8, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Term_getDeclName_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_7, x_8, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_Term_elabPanic___closed__4;
x_31 = l_Lean_addMacroScope(x_28, x_30, x_25);
x_32 = l_Lean_instInhabitedSourceInfo___closed__1;
x_33 = l_Lean_Elab_Term_elabPanic___closed__3;
x_34 = l_Lean_Elab_Term_elabPanic___closed__6;
x_35 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_31);
lean_ctor_set(x_35, 3, x_34);
x_36 = l_Array_empty___closed__1;
x_37 = lean_array_push(x_36, x_35);
x_38 = lean_environment_main_module(x_18);
x_39 = l_Lean_Name_toString___closed__1;
x_40 = l_Lean_Name_toStringWithSep(x_39, x_38);
x_41 = l_Lean_Syntax_mkStrLit(x_40, x_32);
lean_dec(x_40);
x_42 = lean_array_push(x_36, x_41);
x_43 = lean_ctor_get(x_13, 0);
lean_inc(x_43);
x_44 = l_Nat_repr(x_43);
x_45 = l_Lean_numLitKind;
x_46 = l_Lean_Syntax_mkLit(x_45, x_44, x_32);
x_47 = lean_array_push(x_42, x_46);
x_48 = lean_ctor_get(x_13, 1);
lean_inc(x_48);
lean_dec(x_13);
x_49 = l_Nat_repr(x_48);
x_50 = l_Lean_Syntax_mkLit(x_45, x_49, x_32);
x_51 = lean_array_push(x_47, x_50);
x_52 = lean_array_push(x_51, x_11);
x_53 = l_Lean_nullKind___closed__2;
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_array_push(x_37, x_54);
x_56 = l_myMacro____x40_Init_Notation___hyg_1989____closed__4;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Elab_Term_elabPanic___lambda__1(x_1, x_2, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_59 = lean_ctor_get(x_19, 1);
lean_inc(x_59);
lean_dec(x_19);
x_60 = lean_ctor_get(x_20, 0);
lean_inc(x_60);
lean_dec(x_20);
x_61 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_7, x_8, x_59);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Elab_Term_elabPanic___closed__10;
x_70 = l_Lean_addMacroScope(x_67, x_69, x_64);
x_71 = l_Lean_instInhabitedSourceInfo___closed__1;
x_72 = l_Lean_Elab_Term_elabPanic___closed__9;
x_73 = l_Lean_Elab_Term_elabPanic___closed__12;
x_74 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
lean_ctor_set(x_74, 2, x_70);
lean_ctor_set(x_74, 3, x_73);
x_75 = l_Array_empty___closed__1;
x_76 = lean_array_push(x_75, x_74);
x_77 = lean_environment_main_module(x_18);
x_78 = l_Lean_Name_toString___closed__1;
x_79 = l_Lean_Name_toStringWithSep(x_78, x_77);
x_80 = l_Lean_Syntax_mkStrLit(x_79, x_71);
lean_dec(x_79);
x_81 = lean_array_push(x_75, x_80);
x_82 = l_Lean_Name_toStringWithSep(x_78, x_60);
x_83 = l_Lean_Syntax_mkStrLit(x_82, x_71);
lean_dec(x_82);
x_84 = lean_array_push(x_81, x_83);
x_85 = lean_ctor_get(x_13, 0);
lean_inc(x_85);
x_86 = l_Nat_repr(x_85);
x_87 = l_Lean_numLitKind;
x_88 = l_Lean_Syntax_mkLit(x_87, x_86, x_71);
x_89 = lean_array_push(x_84, x_88);
x_90 = lean_ctor_get(x_13, 1);
lean_inc(x_90);
lean_dec(x_13);
x_91 = l_Nat_repr(x_90);
x_92 = l_Lean_Syntax_mkLit(x_87, x_91, x_71);
x_93 = lean_array_push(x_89, x_92);
x_94 = lean_array_push(x_93, x_11);
x_95 = l_Lean_nullKind___closed__2;
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_array_push(x_76, x_96);
x_98 = l_myMacro____x40_Init_Notation___hyg_1989____closed__4;
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = l_Lean_Elab_Term_elabPanic___lambda__1(x_1, x_2, x_99, x_3, x_4, x_5, x_6, x_7, x_8, x_68);
return x_100;
}
}
}
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_getRefPosition___at_Lean_Elab_Term_elabPanic___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_getRefPosition___at_Lean_Elab_Term_elabPanic___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabPanic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabPanic), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabPanic(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_panic___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabPanic___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("panic!");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\"unreachable code has been reached\"");
return x_1;
}
}
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_Elab_Term_expandUnreachable___rarg___closed__1;
lean_inc(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Array_empty___closed__1;
x_9 = lean_array_push(x_8, x_7);
x_10 = l_Lean_Elab_Term_expandUnreachable___rarg___closed__2;
x_11 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_array_push(x_8, x_11);
x_13 = l_Lean_strLitKind___closed__2;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_array_push(x_9, x_14);
x_16 = l_Lean_Parser_Term_panic___elambda__1___closed__2;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_3, 0, x_17);
return x_3;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_20 = l_Lean_Elab_Term_expandUnreachable___rarg___closed__1;
lean_inc(x_18);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Array_empty___closed__1;
x_23 = lean_array_push(x_22, x_21);
x_24 = l_Lean_Elab_Term_expandUnreachable___rarg___closed__2;
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_array_push(x_22, x_25);
x_27 = l_Lean_strLitKind___closed__2;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_array_push(x_23, x_28);
x_30 = l_Lean_Parser_Term_panic___elambda__1___closed__2;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_19);
return x_32;
}
}
}
lean_object* l_Lean_Elab_Term_expandUnreachable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandUnreachable___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_expandUnreachable___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandUnreachable___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_expandUnreachable(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandUnreachable___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandUnreachable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_Lean_Parser_Term_unreachable___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandAssert_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_expandAssert_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandAssert_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("then");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("else");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\"assertion violation\"");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\"assertion violation: \"");
return x_1;
}
}
lean_object* l_Lean_Elab_Term_expandAssert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_unsigned_to_nat(3u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
lean_inc(x_5);
x_8 = l_Lean_Syntax_reprint(x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_termIf_____x3a__Then__Else_____closed__3;
lean_inc(x_11);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Array_empty___closed__1;
x_15 = lean_array_push(x_14, x_13);
x_16 = lean_array_push(x_15, x_5);
x_17 = l_Lean_Elab_Term_expandAssert___closed__1;
lean_inc(x_11);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_push(x_16, x_18);
x_20 = lean_array_push(x_19, x_7);
x_21 = l_Lean_Elab_Term_expandAssert___closed__2;
lean_inc(x_11);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_array_push(x_20, x_22);
x_24 = l_Lean_Elab_Term_expandUnreachable___rarg___closed__1;
lean_inc(x_11);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_array_push(x_14, x_25);
x_27 = l_prec_x28___x29___closed__3;
lean_inc(x_11);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_array_push(x_14, x_28);
x_30 = l_Lean_Elab_Term_expandAssert___closed__3;
lean_inc(x_11);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_push(x_14, x_31);
x_33 = l_Lean_strLitKind___closed__2;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_array_push(x_14, x_34);
x_36 = l_myMacro____x40_Init_Notation___hyg_1192____closed__8;
x_37 = lean_array_push(x_35, x_36);
x_38 = l_Lean_nullKind___closed__2;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_array_push(x_29, x_39);
x_41 = l_prec_x28___x29___closed__7;
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_11);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_array_push(x_40, x_42);
x_44 = l_myMacro____x40_Init_Notation___hyg_11370____closed__8;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_array_push(x_26, x_45);
x_47 = l_Lean_Parser_Term_panic___elambda__1___closed__2;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_array_push(x_23, x_48);
x_50 = l_termIf__Then__Else_____closed__2;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_9, 0, x_51);
return x_9;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_52 = lean_ctor_get(x_9, 0);
x_53 = lean_ctor_get(x_9, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_9);
x_54 = l_termIf_____x3a__Then__Else_____closed__3;
lean_inc(x_52);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Array_empty___closed__1;
x_57 = lean_array_push(x_56, x_55);
x_58 = lean_array_push(x_57, x_5);
x_59 = l_Lean_Elab_Term_expandAssert___closed__1;
lean_inc(x_52);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_array_push(x_58, x_60);
x_62 = lean_array_push(x_61, x_7);
x_63 = l_Lean_Elab_Term_expandAssert___closed__2;
lean_inc(x_52);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_52);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_array_push(x_62, x_64);
x_66 = l_Lean_Elab_Term_expandUnreachable___rarg___closed__1;
lean_inc(x_52);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_52);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_array_push(x_56, x_67);
x_69 = l_prec_x28___x29___closed__3;
lean_inc(x_52);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_52);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_array_push(x_56, x_70);
x_72 = l_Lean_Elab_Term_expandAssert___closed__3;
lean_inc(x_52);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_52);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_array_push(x_56, x_73);
x_75 = l_Lean_strLitKind___closed__2;
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = lean_array_push(x_56, x_76);
x_78 = l_myMacro____x40_Init_Notation___hyg_1192____closed__8;
x_79 = lean_array_push(x_77, x_78);
x_80 = l_Lean_nullKind___closed__2;
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_array_push(x_71, x_81);
x_83 = l_prec_x28___x29___closed__7;
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_52);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_array_push(x_82, x_84);
x_86 = l_myMacro____x40_Init_Notation___hyg_11370____closed__8;
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_array_push(x_68, x_87);
x_89 = l_Lean_Parser_Term_panic___elambda__1___closed__2;
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_array_push(x_65, x_90);
x_92 = l_termIf__Then__Else_____closed__2;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_53);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_8, 0);
lean_inc(x_95);
lean_dec(x_8);
x_96 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = l_termIf_____x3a__Then__Else_____closed__3;
lean_inc(x_98);
x_100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Array_empty___closed__1;
x_102 = lean_array_push(x_101, x_100);
x_103 = lean_array_push(x_102, x_5);
x_104 = l_Lean_Elab_Term_expandAssert___closed__1;
lean_inc(x_98);
x_105 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_105, 0, x_98);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_array_push(x_103, x_105);
x_107 = lean_array_push(x_106, x_7);
x_108 = l_Lean_Elab_Term_expandAssert___closed__2;
lean_inc(x_98);
x_109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_109, 0, x_98);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_array_push(x_107, x_109);
x_111 = l_Lean_Elab_Term_expandUnreachable___rarg___closed__1;
lean_inc(x_98);
x_112 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_112, 0, x_98);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_array_push(x_101, x_112);
x_114 = l_prec_x28___x29___closed__3;
lean_inc(x_98);
x_115 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_115, 0, x_98);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_array_push(x_101, x_115);
x_117 = l_Lean_Elab_Term_expandAssert___closed__4;
lean_inc(x_98);
x_118 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_118, 0, x_98);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_array_push(x_101, x_118);
x_120 = l_Lean_strLitKind___closed__2;
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = lean_array_push(x_101, x_121);
x_123 = l_Lean_Syntax_expandInterpolatedStr___lambda__1___closed__1;
lean_inc(x_98);
x_124 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_124, 0, x_98);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_array_push(x_122, x_124);
x_126 = l_Lean_instInhabitedSourceInfo___closed__1;
x_127 = l_Lean_Syntax_mkStrLit(x_95, x_126);
lean_dec(x_95);
x_128 = lean_array_push(x_125, x_127);
x_129 = l_term___x2b_x2b_____closed__2;
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = lean_array_push(x_101, x_130);
x_132 = l_myMacro____x40_Init_Notation___hyg_1192____closed__8;
x_133 = lean_array_push(x_131, x_132);
x_134 = l_Lean_nullKind___closed__2;
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = lean_array_push(x_116, x_135);
x_137 = l_prec_x28___x29___closed__7;
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_98);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_array_push(x_136, x_138);
x_140 = l_myMacro____x40_Init_Notation___hyg_11370____closed__8;
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = lean_array_push(x_113, x_141);
x_143 = l_Lean_Parser_Term_panic___elambda__1___closed__2;
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = lean_array_push(x_110, x_144);
x_146 = l_termIf__Then__Else_____closed__2;
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
lean_ctor_set(x_96, 0, x_147);
return x_96;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_148 = lean_ctor_get(x_96, 0);
x_149 = lean_ctor_get(x_96, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_96);
x_150 = l_termIf_____x3a__Then__Else_____closed__3;
lean_inc(x_148);
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Array_empty___closed__1;
x_153 = lean_array_push(x_152, x_151);
x_154 = lean_array_push(x_153, x_5);
x_155 = l_Lean_Elab_Term_expandAssert___closed__1;
lean_inc(x_148);
x_156 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_156, 0, x_148);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_array_push(x_154, x_156);
x_158 = lean_array_push(x_157, x_7);
x_159 = l_Lean_Elab_Term_expandAssert___closed__2;
lean_inc(x_148);
x_160 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_160, 0, x_148);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_array_push(x_158, x_160);
x_162 = l_Lean_Elab_Term_expandUnreachable___rarg___closed__1;
lean_inc(x_148);
x_163 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_163, 0, x_148);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_array_push(x_152, x_163);
x_165 = l_prec_x28___x29___closed__3;
lean_inc(x_148);
x_166 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_166, 0, x_148);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_array_push(x_152, x_166);
x_168 = l_Lean_Elab_Term_expandAssert___closed__4;
lean_inc(x_148);
x_169 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_169, 0, x_148);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_array_push(x_152, x_169);
x_171 = l_Lean_strLitKind___closed__2;
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
x_173 = lean_array_push(x_152, x_172);
x_174 = l_Lean_Syntax_expandInterpolatedStr___lambda__1___closed__1;
lean_inc(x_148);
x_175 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_175, 0, x_148);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_array_push(x_173, x_175);
x_177 = l_Lean_instInhabitedSourceInfo___closed__1;
x_178 = l_Lean_Syntax_mkStrLit(x_95, x_177);
lean_dec(x_95);
x_179 = lean_array_push(x_176, x_178);
x_180 = l_term___x2b_x2b_____closed__2;
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
x_182 = lean_array_push(x_152, x_181);
x_183 = l_myMacro____x40_Init_Notation___hyg_1192____closed__8;
x_184 = lean_array_push(x_182, x_183);
x_185 = l_Lean_nullKind___closed__2;
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
x_187 = lean_array_push(x_167, x_186);
x_188 = l_prec_x28___x29___closed__7;
x_189 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_189, 0, x_148);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_array_push(x_187, x_189);
x_191 = l_myMacro____x40_Init_Notation___hyg_11370____closed__8;
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
x_193 = lean_array_push(x_164, x_192);
x_194 = l_Lean_Parser_Term_panic___elambda__1___closed__2;
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
x_196 = lean_array_push(x_161, x_195);
x_197 = l_termIf__Then__Else_____closed__2;
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_149);
return x_199;
}
}
}
}
lean_object* l_Lean_Elab_Term_expandAssert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandAssert(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandAssert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandAssert___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandAssert(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_Lean_Parser_Term_assert___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandAssert___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_dbgTrace___elambda__1___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Term_dbgTrace___elambda__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_expandDbgTrace___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Term_dbgTrace___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandDbgTrace___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandDbgTrace___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandDbgTrace___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandDbgTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_unsigned_to_nat(3u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
lean_inc(x_5);
x_8 = l_Lean_Syntax_getKind(x_5);
x_9 = l_Lean_interpolatedStrKind;
x_10 = lean_name_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Lean_Elab_Term_expandDbgTrace___closed__3;
lean_inc(x_14);
lean_inc(x_15);
x_17 = l_Lean_addMacroScope(x_15, x_16, x_14);
x_18 = l_Lean_instInhabitedSourceInfo___closed__1;
x_19 = l_Lean_Elab_Term_expandDbgTrace___closed__2;
x_20 = l_Lean_Elab_Term_expandDbgTrace___closed__5;
x_21 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_20);
x_22 = l_Array_empty___closed__1;
x_23 = lean_array_push(x_22, x_21);
x_24 = l_prec_x28___x29___closed__3;
lean_inc(x_13);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_array_push(x_22, x_25);
x_27 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_23____closed__8;
x_28 = l_Lean_addMacroScope(x_15, x_27, x_14);
x_29 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_23____closed__7;
x_30 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_23____closed__13;
x_31 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_array_push(x_22, x_31);
x_33 = lean_array_push(x_22, x_5);
x_34 = l_Lean_nullKind___closed__2;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_array_push(x_32, x_35);
x_37 = l_myMacro____x40_Init_Notation___hyg_1989____closed__4;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_array_push(x_22, x_38);
x_40 = l_myMacro____x40_Init_Notation___hyg_1192____closed__8;
x_41 = lean_array_push(x_39, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_34);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_array_push(x_26, x_42);
x_44 = l_prec_x28___x29___closed__7;
lean_inc(x_13);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_13);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_array_push(x_43, x_45);
x_47 = l_myMacro____x40_Init_Notation___hyg_11370____closed__8;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_array_push(x_22, x_48);
x_50 = l_myMacro____x40_Init_Notation___hyg_11370____closed__9;
lean_inc(x_13);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_13);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_array_push(x_22, x_51);
x_53 = l_myMacro____x40_Init_Notation___hyg_11900____closed__14;
lean_inc(x_13);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_13);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_array_push(x_22, x_54);
x_56 = l_myMacro____x40_Init_Notation___hyg_11900____closed__13;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_array_push(x_22, x_57);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_34);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_array_push(x_22, x_59);
x_61 = l_myMacro____x40_Init_Notation___hyg_11370____closed__13;
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_13);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_array_push(x_60, x_62);
x_64 = lean_array_push(x_63, x_7);
x_65 = l_myMacro____x40_Init_Notation___hyg_11370____closed__12;
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = lean_array_push(x_52, x_66);
x_68 = l_myMacro____x40_Init_Notation___hyg_11370____closed__10;
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_array_push(x_49, x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_34);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_array_push(x_23, x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_37);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_11, 0, x_73);
return x_11;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_74 = lean_ctor_get(x_11, 0);
x_75 = lean_ctor_get(x_11, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_11);
x_76 = lean_ctor_get(x_2, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_2, 1);
lean_inc(x_77);
lean_dec(x_2);
x_78 = l_Lean_Elab_Term_expandDbgTrace___closed__3;
lean_inc(x_76);
lean_inc(x_77);
x_79 = l_Lean_addMacroScope(x_77, x_78, x_76);
x_80 = l_Lean_instInhabitedSourceInfo___closed__1;
x_81 = l_Lean_Elab_Term_expandDbgTrace___closed__2;
x_82 = l_Lean_Elab_Term_expandDbgTrace___closed__5;
x_83 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
lean_ctor_set(x_83, 2, x_79);
lean_ctor_set(x_83, 3, x_82);
x_84 = l_Array_empty___closed__1;
x_85 = lean_array_push(x_84, x_83);
x_86 = l_prec_x28___x29___closed__3;
lean_inc(x_74);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_74);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_array_push(x_84, x_87);
x_89 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_23____closed__8;
x_90 = l_Lean_addMacroScope(x_77, x_89, x_76);
x_91 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_23____closed__7;
x_92 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_23____closed__13;
x_93 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_93, 0, x_80);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_93, 2, x_90);
lean_ctor_set(x_93, 3, x_92);
x_94 = lean_array_push(x_84, x_93);
x_95 = lean_array_push(x_84, x_5);
x_96 = l_Lean_nullKind___closed__2;
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = lean_array_push(x_94, x_97);
x_99 = l_myMacro____x40_Init_Notation___hyg_1989____closed__4;
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = lean_array_push(x_84, x_100);
x_102 = l_myMacro____x40_Init_Notation___hyg_1192____closed__8;
x_103 = lean_array_push(x_101, x_102);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_96);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_array_push(x_88, x_104);
x_106 = l_prec_x28___x29___closed__7;
lean_inc(x_74);
x_107 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_107, 0, x_74);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_array_push(x_105, x_107);
x_109 = l_myMacro____x40_Init_Notation___hyg_11370____closed__8;
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = lean_array_push(x_84, x_110);
x_112 = l_myMacro____x40_Init_Notation___hyg_11370____closed__9;
lean_inc(x_74);
x_113 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_113, 0, x_74);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_array_push(x_84, x_113);
x_115 = l_myMacro____x40_Init_Notation___hyg_11900____closed__14;
lean_inc(x_74);
x_116 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_116, 0, x_74);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_array_push(x_84, x_116);
x_118 = l_myMacro____x40_Init_Notation___hyg_11900____closed__13;
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
x_120 = lean_array_push(x_84, x_119);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_96);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_array_push(x_84, x_121);
x_123 = l_myMacro____x40_Init_Notation___hyg_11370____closed__13;
x_124 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_124, 0, x_74);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_array_push(x_122, x_124);
x_126 = lean_array_push(x_125, x_7);
x_127 = l_myMacro____x40_Init_Notation___hyg_11370____closed__12;
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
x_129 = lean_array_push(x_114, x_128);
x_130 = l_myMacro____x40_Init_Notation___hyg_11370____closed__10;
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = lean_array_push(x_111, x_131);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_96);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_array_push(x_85, x_133);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_99);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_75);
return x_136;
}
}
else
{
lean_object* x_137; uint8_t x_138; 
x_137 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_ctor_get(x_2, 2);
lean_inc(x_140);
x_141 = lean_ctor_get(x_2, 1);
lean_inc(x_141);
lean_dec(x_2);
x_142 = l_Lean_Elab_Term_expandDbgTrace___closed__3;
x_143 = l_Lean_addMacroScope(x_141, x_142, x_140);
x_144 = l_Lean_instInhabitedSourceInfo___closed__1;
x_145 = l_Lean_Elab_Term_expandDbgTrace___closed__2;
x_146 = l_Lean_Elab_Term_expandDbgTrace___closed__5;
x_147 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
lean_ctor_set(x_147, 2, x_143);
lean_ctor_set(x_147, 3, x_146);
x_148 = l_Array_empty___closed__1;
x_149 = lean_array_push(x_148, x_147);
x_150 = l_prec_x28___x29___closed__3;
lean_inc(x_139);
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_139);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_array_push(x_148, x_151);
x_153 = l_termS_x21_____closed__3;
lean_inc(x_139);
x_154 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_154, 0, x_139);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_array_push(x_148, x_154);
x_156 = lean_array_push(x_155, x_5);
x_157 = l_termS_x21_____closed__2;
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
x_159 = lean_array_push(x_148, x_158);
x_160 = l_myMacro____x40_Init_Notation___hyg_1192____closed__8;
x_161 = lean_array_push(x_159, x_160);
x_162 = l_Lean_nullKind___closed__2;
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
x_164 = lean_array_push(x_152, x_163);
x_165 = l_prec_x28___x29___closed__7;
lean_inc(x_139);
x_166 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_166, 0, x_139);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_array_push(x_164, x_166);
x_168 = l_myMacro____x40_Init_Notation___hyg_11370____closed__8;
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_167);
x_170 = lean_array_push(x_148, x_169);
x_171 = l_myMacro____x40_Init_Notation___hyg_11370____closed__9;
lean_inc(x_139);
x_172 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_172, 0, x_139);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_array_push(x_148, x_172);
x_174 = l_myMacro____x40_Init_Notation___hyg_11900____closed__14;
lean_inc(x_139);
x_175 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_175, 0, x_139);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_array_push(x_148, x_175);
x_177 = l_myMacro____x40_Init_Notation___hyg_11900____closed__13;
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_176);
x_179 = lean_array_push(x_148, x_178);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_162);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_array_push(x_148, x_180);
x_182 = l_myMacro____x40_Init_Notation___hyg_11370____closed__13;
x_183 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_183, 0, x_139);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_array_push(x_181, x_183);
x_185 = lean_array_push(x_184, x_7);
x_186 = l_myMacro____x40_Init_Notation___hyg_11370____closed__12;
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_185);
x_188 = lean_array_push(x_173, x_187);
x_189 = l_myMacro____x40_Init_Notation___hyg_11370____closed__10;
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
x_191 = lean_array_push(x_170, x_190);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_162);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_array_push(x_149, x_192);
x_194 = l_myMacro____x40_Init_Notation___hyg_1989____closed__4;
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
lean_ctor_set(x_137, 0, x_195);
return x_137;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_196 = lean_ctor_get(x_137, 0);
x_197 = lean_ctor_get(x_137, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_137);
x_198 = lean_ctor_get(x_2, 2);
lean_inc(x_198);
x_199 = lean_ctor_get(x_2, 1);
lean_inc(x_199);
lean_dec(x_2);
x_200 = l_Lean_Elab_Term_expandDbgTrace___closed__3;
x_201 = l_Lean_addMacroScope(x_199, x_200, x_198);
x_202 = l_Lean_instInhabitedSourceInfo___closed__1;
x_203 = l_Lean_Elab_Term_expandDbgTrace___closed__2;
x_204 = l_Lean_Elab_Term_expandDbgTrace___closed__5;
x_205 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
lean_ctor_set(x_205, 2, x_201);
lean_ctor_set(x_205, 3, x_204);
x_206 = l_Array_empty___closed__1;
x_207 = lean_array_push(x_206, x_205);
x_208 = l_prec_x28___x29___closed__3;
lean_inc(x_196);
x_209 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_209, 0, x_196);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_array_push(x_206, x_209);
x_211 = l_termS_x21_____closed__3;
lean_inc(x_196);
x_212 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_212, 0, x_196);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_array_push(x_206, x_212);
x_214 = lean_array_push(x_213, x_5);
x_215 = l_termS_x21_____closed__2;
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_214);
x_217 = lean_array_push(x_206, x_216);
x_218 = l_myMacro____x40_Init_Notation___hyg_1192____closed__8;
x_219 = lean_array_push(x_217, x_218);
x_220 = l_Lean_nullKind___closed__2;
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
x_222 = lean_array_push(x_210, x_221);
x_223 = l_prec_x28___x29___closed__7;
lean_inc(x_196);
x_224 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_224, 0, x_196);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_array_push(x_222, x_224);
x_226 = l_myMacro____x40_Init_Notation___hyg_11370____closed__8;
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_225);
x_228 = lean_array_push(x_206, x_227);
x_229 = l_myMacro____x40_Init_Notation___hyg_11370____closed__9;
lean_inc(x_196);
x_230 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_230, 0, x_196);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_array_push(x_206, x_230);
x_232 = l_myMacro____x40_Init_Notation___hyg_11900____closed__14;
lean_inc(x_196);
x_233 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_233, 0, x_196);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_array_push(x_206, x_233);
x_235 = l_myMacro____x40_Init_Notation___hyg_11900____closed__13;
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_234);
x_237 = lean_array_push(x_206, x_236);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_220);
lean_ctor_set(x_238, 1, x_237);
x_239 = lean_array_push(x_206, x_238);
x_240 = l_myMacro____x40_Init_Notation___hyg_11370____closed__13;
x_241 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_241, 0, x_196);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_array_push(x_239, x_241);
x_243 = lean_array_push(x_242, x_7);
x_244 = l_myMacro____x40_Init_Notation___hyg_11370____closed__12;
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_243);
x_246 = lean_array_push(x_231, x_245);
x_247 = l_myMacro____x40_Init_Notation___hyg_11370____closed__10;
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_246);
x_249 = lean_array_push(x_228, x_248);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_220);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_array_push(x_207, x_250);
x_252 = l_myMacro____x40_Init_Notation___hyg_1989____closed__4;
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_251);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_197);
return x_254;
}
}
}
}
lean_object* l_Lean_Elab_Term_expandDbgTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandDbgTrace(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandDbgTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandDbgTrace___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandDbgTrace(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_Lean_Parser_Term_dbgTrace___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandDbgTrace___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSorry___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkSorry___rarg___lambda__1___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSorry___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_mkSorry___rarg___lambda__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_expandSorry___rarg___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSorry___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSorry___rarg___lambda__1___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSorry___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandSorry___rarg___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSorry___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprBool___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSorry___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_instReprBool___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_expandSorry___rarg___closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSorry___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instQuoteBool___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandSorry___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandSorry___rarg___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandSorry___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Meta_mkSorry___rarg___lambda__1___closed__2;
lean_inc(x_6);
lean_inc(x_7);
x_9 = l_Lean_addMacroScope(x_7, x_8, x_6);
x_10 = l_Lean_instInhabitedSourceInfo___closed__1;
x_11 = l_Lean_Elab_Term_expandSorry___rarg___closed__2;
x_12 = l_Lean_Elab_Term_expandSorry___rarg___closed__4;
x_13 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_12);
x_14 = l_Array_empty___closed__1;
x_15 = lean_array_push(x_14, x_13);
x_16 = l_myMacro____x40_Init_Notation___hyg_11900____closed__14;
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_push(x_14, x_17);
x_19 = l_myMacro____x40_Init_Notation___hyg_11900____closed__13;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_array_push(x_14, x_20);
x_22 = l_Lean_setOptionFromString___closed__4;
x_23 = l_Lean_addMacroScope(x_7, x_22, x_6);
x_24 = l_Lean_Elab_Term_expandSorry___rarg___closed__6;
x_25 = l_Lean_Elab_Term_expandSorry___rarg___closed__8;
x_26 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_26, 0, x_10);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_25);
x_27 = lean_array_push(x_21, x_26);
x_28 = l_Lean_nullKind___closed__2;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_array_push(x_15, x_29);
x_31 = l_myMacro____x40_Init_Notation___hyg_1989____closed__4;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_3, 0, x_32);
return x_3;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_33 = lean_ctor_get(x_3, 0);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_3);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l_Lean_Meta_mkSorry___rarg___lambda__1___closed__2;
lean_inc(x_35);
lean_inc(x_36);
x_38 = l_Lean_addMacroScope(x_36, x_37, x_35);
x_39 = l_Lean_instInhabitedSourceInfo___closed__1;
x_40 = l_Lean_Elab_Term_expandSorry___rarg___closed__2;
x_41 = l_Lean_Elab_Term_expandSorry___rarg___closed__4;
x_42 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_38);
lean_ctor_set(x_42, 3, x_41);
x_43 = l_Array_empty___closed__1;
x_44 = lean_array_push(x_43, x_42);
x_45 = l_myMacro____x40_Init_Notation___hyg_11900____closed__14;
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_33);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_array_push(x_43, x_46);
x_48 = l_myMacro____x40_Init_Notation___hyg_11900____closed__13;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_array_push(x_43, x_49);
x_51 = l_Lean_setOptionFromString___closed__4;
x_52 = l_Lean_addMacroScope(x_36, x_51, x_35);
x_53 = l_Lean_Elab_Term_expandSorry___rarg___closed__6;
x_54 = l_Lean_Elab_Term_expandSorry___rarg___closed__8;
x_55 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_55, 0, x_39);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_52);
lean_ctor_set(x_55, 3, x_54);
x_56 = lean_array_push(x_50, x_55);
x_57 = l_Lean_nullKind___closed__2;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_array_push(x_44, x_58);
x_60 = l_myMacro____x40_Init_Notation___hyg_1989____closed__4;
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_34);
return x_62;
}
}
}
lean_object* l_Lean_Elab_Term_expandSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSorry___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandSorry___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_expandSorry(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandSorry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandSorry___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_14986____closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandSorry___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEmptyC___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("EmptyCollection.emptyCollection");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEmptyC___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_expandEmptyC___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEmptyC___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_expandEmptyC___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_expandEmptyC___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEmptyC___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("EmptyCollection");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEmptyC___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandEmptyC___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEmptyC___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("emptyCollection");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEmptyC___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_expandEmptyC___closed__5;
x_2 = l_Lean_Elab_Term_expandEmptyC___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEmptyC___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandEmptyC___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandEmptyC___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandEmptyC___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandEmptyC(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_10 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Term_expandEmptyC___closed__7;
x_19 = l_Lean_addMacroScope(x_16, x_18, x_13);
x_20 = l_Lean_instInhabitedSourceInfo___closed__1;
x_21 = l_Lean_Elab_Term_expandEmptyC___closed__3;
x_22 = l_Lean_Elab_Term_expandEmptyC___closed__9;
x_23 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_22);
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_3, 3);
lean_inc(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_3, 3, x_27);
x_28 = 1;
x_29 = l_Lean_Elab_Term_elabTerm(x_23, x_2, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_30 = lean_ctor_get(x_3, 0);
x_31 = lean_ctor_get(x_3, 1);
x_32 = lean_ctor_get(x_3, 2);
x_33 = lean_ctor_get(x_3, 3);
x_34 = lean_ctor_get(x_3, 4);
x_35 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_36 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_38 = lean_ctor_get(x_3, 5);
lean_inc(x_38);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_3);
lean_inc(x_23);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_23);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
x_41 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_41, 0, x_30);
lean_ctor_set(x_41, 1, x_31);
lean_ctor_set(x_41, 2, x_32);
lean_ctor_set(x_41, 3, x_40);
lean_ctor_set(x_41, 4, x_34);
lean_ctor_set(x_41, 5, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*6, x_35);
lean_ctor_set_uint8(x_41, sizeof(void*)*6 + 1, x_36);
lean_ctor_set_uint8(x_41, sizeof(void*)*6 + 2, x_37);
x_42 = 1;
x_43 = l_Lean_Elab_Term_elabTerm(x_23, x_2, x_42, x_41, x_4, x_5, x_6, x_7, x_8, x_17);
return x_43;
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandEmptyC___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandEmptyC), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandEmptyC(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_emptyC___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandEmptyC___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkPairs_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Prod.mk");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkPairs_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_mkPairs_loop___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkPairs_loop___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_mkPairs_loop___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_mkPairs_loop___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkPairs_loop___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instQuoteProd___rarg___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkPairs_loop___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_mkPairs_loop___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_mkPairs_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
lean_dec(x_2);
x_11 = l_Lean_instInhabitedSyntax;
x_12 = lean_array_get(x_11, x_1, x_10);
x_13 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_4, x_5);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
x_17 = l_Lean_instQuoteProd___rarg___closed__2;
x_18 = l_Lean_addMacroScope(x_16, x_17, x_15);
x_19 = l_Lean_instInhabitedSourceInfo___closed__1;
x_20 = l_Lean_Elab_Term_mkPairs_loop___closed__3;
x_21 = l_Lean_Elab_Term_mkPairs_loop___closed__5;
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_21);
x_23 = l_Array_empty___closed__1;
x_24 = lean_array_push(x_23, x_22);
x_25 = lean_array_push(x_23, x_12);
x_26 = lean_array_push(x_25, x_3);
x_27 = l_Lean_nullKind___closed__2;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_array_push(x_24, x_28);
x_30 = l_myMacro____x40_Init_Notation___hyg_1989____closed__4;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_2 = x_10;
x_3 = x_31;
x_5 = x_14;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Term_mkPairs_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_mkPairs_loop(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_mkPairs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
lean_dec(x_4);
x_7 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_1);
x_8 = l_Lean_Elab_Term_mkPairs_loop(x_1, x_6, x_7, x_2, x_3);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_mkPairs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_mkPairs(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 == x_3;
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_2 + x_7;
x_2 = x_8;
goto _start;
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
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
uint8_t l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_myMacro____x40_Init_Notation___hyg_11370____closed__8;
x_5 = lean_name_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Parser_Term_cdot___elambda__1___closed__2;
x_7 = lean_name_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
x_11 = 0;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_8, x_8);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
x_13 = 0;
return x_13;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_16 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot___spec__1(x_3, x_14, x_15);
return x_16;
}
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
x_18 = 0;
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_2 < x_1;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_8 = x_3;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = x_11;
lean_inc(x_5);
x_15 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot(x_14, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = 1;
x_21 = x_2 + x_20;
x_22 = x_18;
x_23 = lean_array_uset(x_13, x_2, x_22);
x_2 = x_21;
x_3 = x_23;
x_4 = x_19;
x_6 = x_17;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_5);
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
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 5);
x_5 = lean_box(0);
x_6 = l_Lean_Syntax_getPos(x_4);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = l_myMacro____x40_Init_Notation___hyg_11370____closed__8;
x_8 = lean_name_eq(x_5, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = l_Lean_Parser_Term_cdot___elambda__1___closed__2;
x_13 = lean_name_eq(x_5, x_12);
if (x_13 == 0)
{
lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_array_get_size(x_6);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = x_6;
x_17 = lean_box_usize(x_15);
x_18 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___boxed__const__1;
x_19 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__1___boxed), 6, 3);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_16);
x_20 = x_19;
x_21 = lean_apply_3(x_20, x_2, x_3, x_4);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_23, 0, x_1);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_1, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_21, 0, x_28);
return x_21;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_33 = x_29;
} else {
 lean_dec_ref(x_29);
 x_33 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_31);
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_1);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_free_object(x_1);
lean_dec(x_6);
lean_dec(x_5);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_4, x_40);
x_42 = !lean_is_exclusive(x_3);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_3, 1);
x_44 = lean_ctor_get(x_3, 2);
lean_dec(x_44);
lean_inc(x_4);
lean_inc(x_43);
lean_ctor_set(x_3, 2, x_4);
x_45 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__2(x_2, x_3, x_41);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_47, 1);
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_911____closed__4;
x_52 = l_Lean_addMacroScope(x_43, x_51, x_4);
x_53 = lean_box(0);
x_54 = l_Lean_instInhabitedSourceInfo___closed__1;
x_55 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_911____closed__3;
x_56 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_52);
lean_ctor_set(x_56, 3, x_53);
lean_inc(x_56);
x_57 = lean_array_push(x_49, x_56);
lean_ctor_set(x_47, 1, x_57);
lean_ctor_set(x_47, 0, x_56);
return x_45;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_47, 1);
lean_inc(x_58);
lean_dec(x_47);
x_59 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_911____closed__4;
x_60 = l_Lean_addMacroScope(x_43, x_59, x_4);
x_61 = lean_box(0);
x_62 = l_Lean_instInhabitedSourceInfo___closed__1;
x_63 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_911____closed__3;
x_64 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_61);
lean_inc(x_64);
x_65 = lean_array_push(x_58, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_45, 0, x_66);
return x_45;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_67 = lean_ctor_get(x_45, 0);
x_68 = lean_ctor_get(x_45, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_45);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_71 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_911____closed__4;
x_72 = l_Lean_addMacroScope(x_43, x_71, x_4);
x_73 = lean_box(0);
x_74 = l_Lean_instInhabitedSourceInfo___closed__1;
x_75 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_911____closed__3;
x_76 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_76, 2, x_72);
lean_ctor_set(x_76, 3, x_73);
lean_inc(x_76);
x_77 = lean_array_push(x_69, x_76);
if (lean_is_scalar(x_70)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_70;
}
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_68);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_80 = lean_ctor_get(x_3, 0);
x_81 = lean_ctor_get(x_3, 1);
x_82 = lean_ctor_get(x_3, 3);
x_83 = lean_ctor_get(x_3, 4);
x_84 = lean_ctor_get(x_3, 5);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_81);
x_85 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_85, 0, x_80);
lean_ctor_set(x_85, 1, x_81);
lean_ctor_set(x_85, 2, x_4);
lean_ctor_set(x_85, 3, x_82);
lean_ctor_set(x_85, 4, x_83);
lean_ctor_set(x_85, 5, x_84);
x_86 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__2(x_2, x_85, x_41);
lean_dec(x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_91 = x_87;
} else {
 lean_dec_ref(x_87);
 x_91 = lean_box(0);
}
x_92 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_911____closed__4;
x_93 = l_Lean_addMacroScope(x_81, x_92, x_4);
x_94 = lean_box(0);
x_95 = l_Lean_instInhabitedSourceInfo___closed__1;
x_96 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_911____closed__3;
x_97 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_93);
lean_ctor_set(x_97, 3, x_94);
lean_inc(x_97);
x_98 = lean_array_push(x_90, x_97);
if (lean_is_scalar(x_91)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_91;
}
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
if (lean_is_scalar(x_89)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_89;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_88);
return x_100;
}
}
}
else
{
lean_object* x_101; uint8_t x_102; 
lean_dec(x_1);
x_101 = l_Lean_Parser_Term_cdot___elambda__1___closed__2;
x_102 = lean_name_eq(x_5, x_101);
if (x_102 == 0)
{
lean_object* x_103; size_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_103 = lean_array_get_size(x_6);
x_104 = lean_usize_of_nat(x_103);
lean_dec(x_103);
x_105 = x_6;
x_106 = lean_box_usize(x_104);
x_107 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___boxed__const__1;
x_108 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__1___boxed), 6, 3);
lean_closure_set(x_108, 0, x_106);
lean_closure_set(x_108, 1, x_107);
lean_closure_set(x_108, 2, x_105);
x_109 = x_108;
x_110 = lean_apply_3(x_109, x_2, x_3, x_4);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_113 = x_110;
} else {
 lean_dec_ref(x_110);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
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
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_5);
lean_ctor_set(x_117, 1, x_114);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
if (lean_is_scalar(x_113)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_113;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_112);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_5);
x_120 = lean_ctor_get(x_110, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_110, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_122 = x_110;
} else {
 lean_dec_ref(x_110);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_6);
lean_dec(x_5);
x_124 = lean_unsigned_to_nat(1u);
x_125 = lean_nat_add(x_4, x_124);
x_126 = lean_ctor_get(x_3, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_3, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_3, 3);
lean_inc(x_128);
x_129 = lean_ctor_get(x_3, 4);
lean_inc(x_129);
x_130 = lean_ctor_get(x_3, 5);
lean_inc(x_130);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_131 = x_3;
} else {
 lean_dec_ref(x_3);
 x_131 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_127);
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 6, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_126);
lean_ctor_set(x_132, 1, x_127);
lean_ctor_set(x_132, 2, x_4);
lean_ctor_set(x_132, 3, x_128);
lean_ctor_set(x_132, 4, x_129);
lean_ctor_set(x_132, 5, x_130);
x_133 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__2(x_2, x_132, x_125);
lean_dec(x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_138 = x_134;
} else {
 lean_dec_ref(x_134);
 x_138 = lean_box(0);
}
x_139 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_911____closed__4;
x_140 = l_Lean_addMacroScope(x_127, x_139, x_4);
x_141 = lean_box(0);
x_142 = l_Lean_instInhabitedSourceInfo___closed__1;
x_143 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_911____closed__3;
x_144 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_144, 2, x_140);
lean_ctor_set(x_144, 3, x_141);
lean_inc(x_144);
x_145 = lean_array_push(x_137, x_144);
if (lean_is_scalar(x_138)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_138;
}
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
if (lean_is_scalar(x_136)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_136;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_135);
return x_147;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_1);
lean_ctor_set(x_148, 1, x_2);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_4);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_3);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_1);
lean_ctor_set(x_150, 1, x_2);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_4);
return x_151;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__1(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_expandCDot_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Term_expandCDot_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandCDot_x3f_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandCDot_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Array_empty___closed__1;
lean_inc(x_2);
x_8 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot(x_1, x_7, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
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
x_13 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_10);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_myMacro____x40_Init_Notation___hyg_11370____closed__9;
lean_inc(x_15);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_push(x_7, x_17);
x_19 = l_Array_appendCore___rarg(x_7, x_12);
lean_dec(x_12);
x_20 = l_Lean_nullKind___closed__2;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_array_push(x_7, x_21);
x_23 = l_myMacro____x40_Init_Notation___hyg_11370____closed__13;
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_array_push(x_22, x_24);
x_26 = lean_array_push(x_25, x_11);
x_27 = l_myMacro____x40_Init_Notation___hyg_11370____closed__12;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_array_push(x_18, x_28);
x_30 = l_myMacro____x40_Init_Notation___hyg_11370____closed__10;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_13, 0, x_32);
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = l_myMacro____x40_Init_Notation___hyg_11370____closed__9;
lean_inc(x_33);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_array_push(x_7, x_36);
x_38 = l_Array_appendCore___rarg(x_7, x_12);
lean_dec(x_12);
x_39 = l_Lean_nullKind___closed__2;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_array_push(x_7, x_40);
x_42 = l_myMacro____x40_Init_Notation___hyg_11370____closed__13;
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_array_push(x_41, x_43);
x_45 = lean_array_push(x_44, x_11);
x_46 = l_myMacro____x40_Init_Notation___hyg_11370____closed__12;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_array_push(x_37, x_47);
x_49 = l_myMacro____x40_Init_Notation___hyg_11370____closed__10;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_34);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_8);
if (x_53 == 0)
{
return x_8;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_8, 0);
x_55 = lean_ctor_get(x_8, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_8);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 3);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 3, x_12);
x_13 = l_Lean_throwError___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_20 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 3, x_20);
lean_ctor_set(x_21, 4, x_18);
lean_ctor_set(x_21, 5, x_19);
x_22 = l_Lean_throwError___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__2(x_2, x_3, x_4, x_5, x_6, x_21, x_8, x_9);
lean_dec(x_21);
return x_22;
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__3___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__3___rarg), 1, 0);
return x_7;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_36 = lean_st_ref_get(x_8, x_9);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_7, 3);
lean_inc(x_40);
x_41 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_7, 2);
lean_inc(x_45);
x_46 = lean_st_ref_get(x_8, x_43);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_39);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_50, 0, x_39);
x_51 = x_50;
x_52 = lean_environment_main_module(x_39);
x_53 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_42);
lean_ctor_set(x_53, 3, x_44);
lean_ctor_set(x_53, 4, x_45);
lean_ctor_set(x_53, 5, x_40);
lean_inc(x_1);
x_54 = l_Lean_Elab_Term_expandCDot_x3f(x_1, x_53, x_49);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_st_ref_take(x_8, x_48);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_58, 1);
lean_dec(x_61);
lean_ctor_set(x_58, 1, x_56);
x_62 = lean_st_ref_set(x_8, x_58, x_59);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_10 = x_55;
x_11 = x_63;
goto block_35;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_58, 0);
x_65 = lean_ctor_get(x_58, 2);
x_66 = lean_ctor_get(x_58, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_58);
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_56);
lean_ctor_set(x_67, 2, x_65);
lean_ctor_set(x_67, 3, x_66);
x_68 = lean_st_ref_set(x_8, x_67, x_59);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_10 = x_55;
x_11 = x_69;
goto block_35;
}
}
else
{
lean_object* x_70; 
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_ctor_get(x_54, 0);
lean_inc(x_70);
lean_dec(x_54);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = l_Lean_throwErrorAt___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__1(x_71, x_74, x_3, x_4, x_5, x_6, x_7, x_8, x_48);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_71);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
return x_75;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; uint8_t x_81; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_80 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__3___rarg(x_48);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
return x_80;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_80);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
block_35:
{
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_12; lean_object* x_13; 
x_12 = 1;
x_13 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_3, 3);
lean_inc(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_3, 3, x_18);
x_19 = 1;
x_20 = l_Lean_Elab_Term_elabTerm(x_14, x_2, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_3, 3);
x_25 = lean_ctor_get(x_3, 4);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_29 = lean_ctor_get(x_3, 5);
lean_inc(x_29);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
lean_inc(x_14);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_14);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
x_32 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_22);
lean_ctor_set(x_32, 2, x_23);
lean_ctor_set(x_32, 3, x_31);
lean_ctor_set(x_32, 4, x_25);
lean_ctor_set(x_32, 5, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*6, x_26);
lean_ctor_set_uint8(x_32, sizeof(void*)*6 + 1, x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*6 + 2, x_28);
x_33 = 1;
x_34 = l_Lean_Elab_Term_elabTerm(x_14, x_2, x_33, x_32, x_4, x_5, x_6, x_7, x_8, x_11);
return x_34;
}
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabParen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected parentheses notation");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabParen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabParen___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabParen___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabParen___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabParen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_33; uint8_t x_34; 
x_33 = l_myMacro____x40_Init_Notation___hyg_11370____closed__8;
lean_inc(x_1);
x_34 = l_Lean_Syntax_isOfKind(x_1, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_2);
lean_dec(x_1);
x_35 = l_Lean_Elab_Term_elabParen___closed__3;
x_36 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_138; uint8_t x_139; 
x_37 = lean_unsigned_to_nat(1u);
x_38 = l_Lean_Syntax_getArg(x_1, x_37);
x_138 = l_Lean_nullKind___closed__2;
lean_inc(x_38);
x_139 = l_Lean_Syntax_isOfKind(x_38, x_138);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_box(0);
x_39 = x_140;
goto block_137;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_141 = l_Lean_Syntax_getArgs(x_38);
x_142 = lean_array_get_size(x_141);
lean_dec(x_141);
x_143 = lean_unsigned_to_nat(0u);
x_144 = lean_nat_dec_eq(x_142, x_143);
lean_dec(x_142);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_box(0);
x_39 = x_145;
goto block_137;
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_146 = l_Lean_instToExprUnit___lambda__1___closed__3;
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_9);
return x_147;
}
}
block_137:
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_39);
x_40 = l_Lean_nullKind___closed__2;
lean_inc(x_38);
x_41 = l_Lean_Syntax_isOfKind(x_38, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_38);
lean_dec(x_2);
lean_dec(x_1);
x_42 = l_Lean_Elab_Term_elabParen___closed__3;
x_43 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = l_Lean_Syntax_getArgs(x_38);
x_45 = lean_array_get_size(x_44);
lean_dec(x_44);
x_46 = lean_unsigned_to_nat(2u);
x_47 = lean_nat_dec_eq(x_45, x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_38);
lean_dec(x_2);
lean_dec(x_1);
x_48 = l_Lean_Elab_Term_elabParen___closed__3;
x_49 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_64; 
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_Syntax_getArg(x_38, x_50);
x_52 = l_Lean_Syntax_getArg(x_38, x_37);
lean_dec(x_38);
lean_inc(x_52);
x_64 = l_Lean_Syntax_isOfKind(x_52, x_40);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_1);
x_65 = lean_box(0);
x_53 = x_65;
goto block_63;
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = l_Lean_Syntax_getArgs(x_52);
x_67 = lean_array_get_size(x_66);
lean_dec(x_66);
x_68 = lean_nat_dec_eq(x_67, x_37);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_1);
x_69 = lean_box(0);
x_53 = x_69;
goto block_63;
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = l_Lean_Syntax_getArg(x_52, x_50);
lean_dec(x_52);
x_71 = l_myMacro____x40_Init_Notation___hyg_12817____closed__8;
lean_inc(x_70);
x_72 = l_Lean_Syntax_isOfKind(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = l_Lean_Parser_Term_tupleTail___elambda__1___closed__2;
lean_inc(x_70);
x_74 = l_Lean_Syntax_isOfKind(x_70, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_70);
lean_dec(x_51);
lean_dec(x_2);
lean_dec(x_1);
x_75 = l_Lean_Elab_Term_elabParen___closed__3;
x_76 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_75, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_77 = l_Lean_Syntax_getArg(x_70, x_37);
lean_dec(x_70);
x_78 = l_Lean_Syntax_getArgs(x_77);
lean_dec(x_77);
x_79 = l_Lean_mkOptionalNode___closed__2;
x_80 = lean_array_push(x_79, x_51);
x_81 = l_Lean_Syntax_SepArray_getElems___rarg(x_78);
lean_dec(x_78);
x_82 = l_Array_append___rarg(x_80, x_81);
lean_dec(x_81);
x_83 = lean_st_ref_get(x_8, x_9);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_7, 3);
lean_inc(x_87);
x_88 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_85);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_7, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_7, 2);
lean_inc(x_92);
x_93 = lean_st_ref_get(x_8, x_90);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
lean_inc(x_86);
x_97 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_97, 0, x_86);
x_98 = x_97;
x_99 = lean_environment_main_module(x_86);
x_100 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_100, 2, x_89);
lean_ctor_set(x_100, 3, x_91);
lean_ctor_set(x_100, 4, x_92);
lean_ctor_set(x_100, 5, x_87);
x_101 = l_Lean_Elab_Term_mkPairs(x_82, x_100, x_96);
lean_dec(x_82);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_st_ref_take(x_8, x_95);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = !lean_is_exclusive(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_105, 1);
lean_dec(x_108);
lean_ctor_set(x_105, 1, x_103);
x_109 = lean_st_ref_set(x_8, x_105, x_106);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_10 = x_102;
x_11 = x_110;
goto block_32;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_105, 0);
x_112 = lean_ctor_get(x_105, 2);
x_113 = lean_ctor_get(x_105, 3);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_105);
x_114 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_103);
lean_ctor_set(x_114, 2, x_112);
lean_ctor_set(x_114, 3, x_113);
x_115 = lean_st_ref_set(x_8, x_114, x_106);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_10 = x_102;
x_11 = x_116;
goto block_32;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; 
lean_dec(x_2);
lean_dec(x_1);
x_117 = l_Lean_Syntax_getArg(x_70, x_37);
lean_dec(x_70);
x_118 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabType), 8, 1);
lean_closure_set(x_118, 0, x_117);
x_119 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_120 = l_Lean_Elab_Term_withSynthesize___rarg(x_118, x_119, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_121);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_123);
x_124 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot(x_51, x_123, x_3, x_4, x_5, x_6, x_7, x_8, x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_box(0);
x_128 = l_Lean_Elab_Term_ensureHasType(x_123, x_125, x_127, x_3, x_4, x_5, x_6, x_7, x_8, x_126);
return x_128;
}
else
{
uint8_t x_129; 
lean_dec(x_123);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_129 = !lean_is_exclusive(x_124);
if (x_129 == 0)
{
return x_124;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_124, 0);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_124);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_51);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_133 = !lean_is_exclusive(x_120);
if (x_133 == 0)
{
return x_120;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_120, 0);
x_135 = lean_ctor_get(x_120, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_120);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
}
block_63:
{
uint8_t x_54; 
lean_dec(x_53);
lean_inc(x_52);
x_54 = l_Lean_Syntax_isOfKind(x_52, x_40);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_2);
x_55 = l_Lean_Elab_Term_elabParen___closed__3;
x_56 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = l_Lean_Syntax_getArgs(x_52);
lean_dec(x_52);
x_58 = lean_array_get_size(x_57);
lean_dec(x_57);
x_59 = lean_nat_dec_eq(x_58, x_50);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_51);
lean_dec(x_2);
x_60 = l_Lean_Elab_Term_elabParen___closed__3;
x_61 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_60, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_61;
}
else
{
lean_object* x_62; 
x_62 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot(x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_62;
}
}
}
}
}
}
}
block_32:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_3, 3);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_3, 3, x_15);
x_16 = 1;
x_17 = l_Lean_Elab_Term_elabTerm(x_10, x_2, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 2);
x_21 = lean_ctor_get(x_3, 3);
x_22 = lean_ctor_get(x_3, 4);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_25 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 2);
x_26 = lean_ctor_get(x_3, 5);
lean_inc(x_26);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
lean_inc(x_10);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_10);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
x_29 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_19);
lean_ctor_set(x_29, 2, x_20);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set(x_29, 4, x_22);
lean_ctor_set(x_29, 5, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*6, x_23);
lean_ctor_set_uint8(x_29, sizeof(void*)*6 + 1, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*6 + 2, x_25);
x_30 = 1;
x_31 = l_Lean_Elab_Term_elabTerm(x_10, x_2, x_30, x_29, x_4, x_5, x_6, x_7, x_8, x_11);
return x_31;
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabParen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabParen), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabParen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_myMacro____x40_Init_Notation___hyg_11370____closed__8;
x_4 = l___regBuiltin_Lean_Elab_Term_elabParen___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabSubst_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Term_elabSubst_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabSubst_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_3(x_3, x_8, x_9, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Elab_Term_elabSubst_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_elabSubst___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_1, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Meta_instantiateMVars(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Expr_isFVar(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_11);
x_16 = l_Lean_Expr_toHeadIndex(x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_17);
x_19 = lean_st_ref_get(x_9, x_14);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_st_mk_ref(x_21, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_9);
x_25 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_16, x_18, x_13, x_17, x_23, x_6, x_7, x_8, x_9, x_24);
lean_dec(x_18);
lean_dec(x_16);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_9, x_27);
lean_dec(x_9);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_get(x_23, x_29);
lean_dec(x_23);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_26);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_23);
lean_dec(x_9);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_box(0);
x_40 = l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_15_(x_3, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_11);
x_41 = l_Lean_Expr_toHeadIndex(x_2);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_42);
x_44 = lean_st_ref_get(x_9, x_14);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_st_mk_ref(x_46, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_9);
x_50 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_41, x_43, x_13, x_42, x_48, x_6, x_7, x_8, x_9, x_49);
lean_dec(x_43);
lean_dec(x_41);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_st_ref_get(x_9, x_52);
lean_dec(x_9);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_st_ref_get(x_48, x_54);
lean_dec(x_48);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_51);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_48);
lean_dec(x_9);
x_60 = !lean_is_exclusive(x_50);
if (x_60 == 0)
{
return x_50;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_50, 0);
x_62 = lean_ctor_get(x_50, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_50);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_64 = l_Lean_mkOptionalNode___closed__2;
x_65 = lean_array_push(x_64, x_2);
x_66 = lean_expr_abstract(x_13, x_65);
lean_dec(x_65);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_66);
return x_11;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_11, 0);
x_68 = lean_ctor_get(x_11, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_11);
x_69 = l_Lean_Expr_isFVar(x_2);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_70 = l_Lean_Expr_toHeadIndex(x_2);
x_71 = lean_unsigned_to_nat(0u);
x_72 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_71);
x_73 = lean_st_ref_get(x_9, x_68);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_st_mk_ref(x_75, x_74);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_9);
x_79 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_70, x_72, x_67, x_71, x_77, x_6, x_7, x_8, x_9, x_78);
lean_dec(x_72);
lean_dec(x_70);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_st_ref_get(x_9, x_81);
lean_dec(x_9);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_st_ref_get(x_77, x_83);
lean_dec(x_77);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_77);
lean_dec(x_9);
x_88 = lean_ctor_get(x_79, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_79, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_90 = x_79;
} else {
 lean_dec_ref(x_79);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_box(0);
x_93 = l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_15_(x_3, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_94 = l_Lean_Expr_toHeadIndex(x_2);
x_95 = lean_unsigned_to_nat(0u);
x_96 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_95);
x_97 = lean_st_ref_get(x_9, x_68);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_st_mk_ref(x_99, x_98);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_9);
x_103 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_94, x_96, x_67, x_95, x_101, x_6, x_7, x_8, x_9, x_102);
lean_dec(x_96);
lean_dec(x_94);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_st_ref_get(x_9, x_105);
lean_dec(x_9);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_st_ref_get(x_101, x_107);
lean_dec(x_101);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_104);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_101);
lean_dec(x_9);
x_112 = lean_ctor_get(x_103, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_103, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_114 = x_103;
} else {
 lean_dec_ref(x_103);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_116 = l_Lean_mkOptionalNode___closed__2;
x_117 = lean_array_push(x_116, x_2);
x_118 = lean_expr_abstract(x_67, x_117);
lean_dec(x_117);
lean_dec(x_67);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_68);
return x_119;
}
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_11);
if (x_120 == 0)
{
return x_11;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_11, 0);
x_122 = lean_ctor_get(x_11, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_11);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabSubst___spec__3___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg___lambda__1), 9, 3);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabSubst___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabSubst___spec__3___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Elab_Term_elabSubst___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Meta_instantiateMVars(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Expr_isFVar(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_11);
x_16 = l_Lean_Expr_toHeadIndex(x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_17);
x_19 = lean_st_ref_get(x_9, x_14);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_st_mk_ref(x_21, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_9);
x_25 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_16, x_18, x_13, x_17, x_23, x_6, x_7, x_8, x_9, x_24);
lean_dec(x_18);
lean_dec(x_16);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_9, x_27);
lean_dec(x_9);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_get(x_23, x_29);
lean_dec(x_23);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_26);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_23);
lean_dec(x_9);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_box(0);
x_40 = l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_15_(x_3, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_11);
x_41 = l_Lean_Expr_toHeadIndex(x_2);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_42);
x_44 = lean_st_ref_get(x_9, x_14);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_st_mk_ref(x_46, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_9);
x_50 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_41, x_43, x_13, x_42, x_48, x_6, x_7, x_8, x_9, x_49);
lean_dec(x_43);
lean_dec(x_41);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_st_ref_get(x_9, x_52);
lean_dec(x_9);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_st_ref_get(x_48, x_54);
lean_dec(x_48);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_51);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_48);
lean_dec(x_9);
x_60 = !lean_is_exclusive(x_50);
if (x_60 == 0)
{
return x_50;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_50, 0);
x_62 = lean_ctor_get(x_50, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_50);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_64 = l_Lean_mkOptionalNode___closed__2;
x_65 = lean_array_push(x_64, x_2);
x_66 = lean_expr_abstract(x_13, x_65);
lean_dec(x_65);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_66);
return x_11;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_11, 0);
x_68 = lean_ctor_get(x_11, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_11);
x_69 = l_Lean_Expr_isFVar(x_2);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_70 = l_Lean_Expr_toHeadIndex(x_2);
x_71 = lean_unsigned_to_nat(0u);
x_72 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_71);
x_73 = lean_st_ref_get(x_9, x_68);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_st_mk_ref(x_75, x_74);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_9);
x_79 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_70, x_72, x_67, x_71, x_77, x_6, x_7, x_8, x_9, x_78);
lean_dec(x_72);
lean_dec(x_70);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_st_ref_get(x_9, x_81);
lean_dec(x_9);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_st_ref_get(x_77, x_83);
lean_dec(x_77);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_77);
lean_dec(x_9);
x_88 = lean_ctor_get(x_79, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_79, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_90 = x_79;
} else {
 lean_dec_ref(x_79);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_box(0);
x_93 = l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_15_(x_3, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_94 = l_Lean_Expr_toHeadIndex(x_2);
x_95 = lean_unsigned_to_nat(0u);
x_96 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_95);
x_97 = lean_st_ref_get(x_9, x_68);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_st_mk_ref(x_99, x_98);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_9);
x_103 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_94, x_96, x_67, x_95, x_101, x_6, x_7, x_8, x_9, x_102);
lean_dec(x_96);
lean_dec(x_94);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_st_ref_get(x_9, x_105);
lean_dec(x_9);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_st_ref_get(x_101, x_107);
lean_dec(x_101);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_104);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_101);
lean_dec(x_9);
x_112 = lean_ctor_get(x_103, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_103, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_114 = x_103;
} else {
 lean_dec_ref(x_103);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_116 = l_Lean_mkOptionalNode___closed__2;
x_117 = lean_array_push(x_116, x_2);
x_118 = lean_expr_abstract(x_67, x_117);
lean_dec(x_117);
lean_dec(x_67);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_68);
return x_119;
}
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_11);
if (x_120 == 0)
{
return x_11;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_11, 0);
x_122 = lean_ctor_get(x_11, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_11);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Elab_Term_elabSubst___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2);
x_11 = lean_array_push(x_10, x_2);
x_12 = lean_expr_instantiate1(x_1, x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_mkLambdaFVars(x_11, x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst___lambda__1___boxed), 9, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_16 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabSubst___spec__3___rarg(x_2, x_15, x_3, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_19 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(x_4, x_9, x_10, x_11, x_12, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp(x_17, x_5, x_20, x_9, x_10, x_11, x_12, x_21);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_expr_instantiate1(x_1, x_2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_18 = l_Lean_Meta_isExprDefEq(x_3, x_17, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_4);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_box(0);
x_27 = l_Lean_Elab_Term_elabSubst___lambda__2(x_1, x_5, x_6, x_7, x_8, x_26, x_10, x_11, x_12, x_13, x_14, x_15, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_30 = lean_expr_instantiate1(x_8, x_5);
lean_inc(x_30);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_ctor_get(x_14, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_14, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_14, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_14, 4);
lean_inc(x_36);
x_37 = lean_ctor_get(x_14, 5);
lean_inc(x_37);
x_38 = l_Lean_replaceRef(x_3, x_35);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_34);
lean_ctor_set(x_39, 3, x_38);
lean_ctor_set(x_39, 4, x_36);
lean_ctor_set(x_39, 5, x_37);
x_40 = 1;
lean_inc(x_15);
lean_inc(x_39);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_31);
x_41 = l_Lean_Elab_Term_elabTerm(x_3, x_31, x_40, x_10, x_11, x_12, x_13, x_39, x_15, x_16);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_15);
lean_inc(x_39);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_42);
x_44 = l_Lean_Elab_Term_ensureHasType(x_31, x_42, x_4, x_10, x_11, x_12, x_13, x_39, x_15, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_6);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_17 = x_45;
x_18 = x_46;
goto block_29;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
lean_inc(x_15);
lean_inc(x_39);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_42);
x_49 = l_Lean_Meta_inferType(x_42, x_12, x_13, x_39, x_15, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_box(0);
lean_inc(x_15);
lean_inc(x_39);
lean_inc(x_13);
lean_inc(x_12);
x_53 = l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__5(x_50, x_6, x_52, x_10, x_11, x_12, x_13, x_39, x_15, x_51);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
x_57 = l_Lean_Expr_hasLooseBVars(x_55);
if (x_57 == 0)
{
lean_dec(x_55);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set_tag(x_53, 1);
lean_ctor_set(x_53, 0, x_47);
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_free_object(x_53);
x_58 = lean_box(0);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_59 = l_Lean_Elab_Term_elabSubst___lambda__3(x_55, x_5, x_30, x_47, x_1, x_2, x_7, x_42, x_58, x_10, x_11, x_12, x_13, x_39, x_15, x_56);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_17 = x_60;
x_18 = x_61;
goto block_29;
}
else
{
uint8_t x_62; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_59);
if (x_62 == 0)
{
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_53, 0);
x_67 = lean_ctor_get(x_53, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_53);
x_68 = l_Lean_Expr_hasLooseBVars(x_66);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_66);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_47);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_box(0);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_71 = l_Lean_Elab_Term_elabSubst___lambda__3(x_66, x_5, x_30, x_47, x_1, x_2, x_7, x_42, x_70, x_10, x_11, x_12, x_13, x_39, x_15, x_67);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_17 = x_72;
x_18 = x_73;
goto block_29;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
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
}
}
else
{
uint8_t x_78; 
lean_dec(x_47);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_53);
if (x_78 == 0)
{
return x_53;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_53, 0);
x_80 = lean_ctor_get(x_53, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_53);
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
lean_dec(x_47);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_49);
if (x_82 == 0)
{
return x_49;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_49, 0);
x_84 = lean_ctor_get(x_49, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_49);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_41);
if (x_86 == 0)
{
return x_41;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_41, 0);
x_88 = lean_ctor_get(x_41, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_41);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
block_29:
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst___lambda__1___boxed), 9, 1);
lean_closure_set(x_19, 0, x_8);
x_20 = 0;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_21 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabSubst___spec__3___rarg(x_1, x_20, x_2, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp(x_22, x_17, x_7, x_12, x_13, x_14, x_15, x_23);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
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
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_14 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(x_5, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_apply_12(x_1, x_4, x_3, x_15, x_2, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSubst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid `▸` notation");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSubst___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid `▸` notation, argument");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSubst___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabSubst___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSubst___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nequality expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSubst___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabSubst___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSubst___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid `▸` notation, expected type");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSubst___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabSubst___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSubst___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\ndoes contain equation left-hand-side nor right-hand-side");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSubst___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabSubst___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabSubst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_elabSubst___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_11 = l_Lean_Elab_Term_tryPostponeIfHasMVars(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Parser_Term_subst___elambda__1___closed__1;
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
lean_dec(x_1);
x_21 = l_Lean_nullKind___closed__2;
lean_inc(x_20);
x_22 = l_Lean_Syntax_isOfKind(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_13);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = l_Lean_Syntax_getArgs(x_20);
x_25 = lean_array_get_size(x_24);
lean_dec(x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_dec_eq(x_25, x_26);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_13);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_29 = l_Lean_Syntax_getArg(x_20, x_17);
lean_dec(x_20);
x_30 = lean_box(0);
x_31 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_32 = l_Lean_Elab_Term_elabTerm(x_18, x_30, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_33);
x_35 = l_Lean_Meta_inferType(x_33, x_5, x_6, x_7, x_8, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_38 = l_Lean_Meta_instantiateMVars(x_36, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_39);
x_41 = l_Lean_Meta_matchEq_x3f(x_39, x_5, x_6, x_7, x_8, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_29);
lean_dec(x_12);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_indentExpr(x_33);
x_45 = l_Lean_Elab_Term_elabSubst___closed__3;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__8;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_indentExpr(x_39);
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Elab_Term_elabSubst___closed__5;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_54 = lean_ctor_get(x_42, 0);
lean_inc(x_54);
lean_dec(x_42);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
lean_dec(x_41);
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
x_60 = l_Lean_Meta_mkArrow___closed__2;
x_61 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_60, x_7, x_8, x_56);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_59);
lean_inc(x_12);
x_65 = l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__2(x_12, x_59, x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_29);
lean_inc(x_57);
lean_inc(x_62);
x_68 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst___lambda__4___boxed), 16, 4);
lean_closure_set(x_68, 0, x_62);
lean_closure_set(x_68, 1, x_57);
lean_closure_set(x_68, 2, x_29);
lean_closure_set(x_68, 3, x_30);
x_69 = l_Lean_Expr_hasLooseBVars(x_66);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_66);
lean_dec(x_62);
lean_dec(x_57);
lean_dec(x_29);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_58);
lean_inc(x_12);
x_70 = l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__2(x_12, x_58, x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_67);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Expr_hasLooseBVars(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_33);
x_74 = l_Lean_indentExpr(x_12);
x_75 = l_Lean_Elab_Term_elabSubst___closed__7;
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l_Lean_Elab_Term_elabSubst___closed__9;
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_indentExpr(x_39);
x_80 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_KernelException_toMessageData___closed__15;
x_82 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_82, x_3, x_4, x_5, x_6, x_7, x_8, x_72);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
return x_83;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_83);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_39);
lean_dec(x_12);
x_88 = lean_box(0);
x_89 = l_Lean_Elab_Term_elabSubst___lambda__5(x_68, x_71, x_58, x_59, x_33, x_88, x_3, x_4, x_5, x_6, x_7, x_8, x_72);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_68);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_39);
lean_dec(x_33);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_90 = !lean_is_exclusive(x_70);
if (x_90 == 0)
{
return x_70;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_70, 0);
x_92 = lean_ctor_get(x_70, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_70);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_68);
lean_dec(x_39);
lean_dec(x_12);
x_94 = lean_box(0);
x_95 = l_Lean_Elab_Term_elabSubst___lambda__4(x_62, x_57, x_29, x_30, x_58, x_59, x_33, x_66, x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_67);
lean_dec(x_58);
return x_95;
}
}
else
{
uint8_t x_96; 
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_39);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_96 = !lean_is_exclusive(x_65);
if (x_96 == 0)
{
return x_65;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_65, 0);
x_98 = lean_ctor_get(x_65, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_65);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_39);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_100 = !lean_is_exclusive(x_41);
if (x_100 == 0)
{
return x_41;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_41, 0);
x_102 = lean_ctor_get(x_41, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_41);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_104 = !lean_is_exclusive(x_38);
if (x_104 == 0)
{
return x_38;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_38, 0);
x_106 = lean_ctor_get(x_38, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_38);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_108 = !lean_is_exclusive(x_35);
if (x_108 == 0)
{
return x_35;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_35, 0);
x_110 = lean_ctor_get(x_35, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_35);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = !lean_is_exclusive(x_32);
if (x_112 == 0)
{
return x_32;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_32, 0);
x_114 = lean_ctor_get(x_32, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_32);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_11);
if (x_116 == 0)
{
return x_11;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_11, 0);
x_118 = lean_ctor_get(x_11, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_11);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
lean_object* l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_elabSubst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_elabSubst___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabSubst___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabSubst___spec__3___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Elab_Term_elabSubst___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_mkEqNDRec___at_Lean_Elab_Term_elabSubst___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_kabstract___at_Lean_Elab_Term_elabSubst___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Elab_Term_elabSubst___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkEqSymm___at_Lean_Elab_Term_elabSubst___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabSubst___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Term_elabSubst___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_14;
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Term_elabSubst___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
lean_dec(x_2);
return x_17;
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Term_elabSubst___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
lean_dec(x_5);
return x_17;
}
}
lean_object* l_Lean_Elab_Term_elabSubst___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Term_elabSubst___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_14;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSubst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSubst), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabSubst(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_subst___elambda__1___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_elabSubst___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_mkAppM___at_Lean_Elab_Term_elabStateRefT___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed), 6, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___rarg___lambda__1), 9, 3);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_11);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_12);
x_215 = lean_st_ref_get(x_8, x_9);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_216, 3);
lean_inc(x_217);
lean_dec(x_216);
x_218 = lean_ctor_get_uint8(x_217, sizeof(void*)*1);
lean_dec(x_217);
if (x_218 == 0)
{
lean_object* x_219; uint8_t x_220; 
x_219 = lean_ctor_get(x_215, 1);
lean_inc(x_219);
lean_dec(x_215);
x_220 = 0;
x_14 = x_220;
x_15 = x_219;
goto block_214;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_221 = lean_ctor_get(x_215, 1);
lean_inc(x_221);
lean_dec(x_215);
x_222 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_11, x_5, x_6, x_7, x_8, x_221);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_unbox(x_223);
lean_dec(x_223);
x_14 = x_225;
x_15 = x_224;
goto block_214;
}
block_214:
{
if (x_14 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_st_ref_get(x_8, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
lean_dec(x_18);
x_21 = lean_st_ref_take(x_8, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_22, 3);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = 0;
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_28);
x_29 = lean_st_ref_set(x_8, x_22, x_24);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
lean_inc(x_8);
x_31 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__1___rarg(x_13, x_5, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_8, x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_take(x_8, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_37, 3);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_20);
x_43 = lean_st_ref_set(x_8, x_37, x_39);
lean_dec(x_8);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_32);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_32);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_20);
lean_ctor_set(x_37, 3, x_49);
x_50 = lean_st_ref_set(x_8, x_37, x_39);
lean_dec(x_8);
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
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_32);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_54 = lean_ctor_get(x_37, 0);
x_55 = lean_ctor_get(x_37, 1);
x_56 = lean_ctor_get(x_37, 2);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_37);
x_57 = lean_ctor_get(x_38, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_58 = x_38;
} else {
 lean_dec_ref(x_38);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 1, 1);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_20);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_60, 2, x_56);
lean_ctor_set(x_60, 3, x_59);
x_61 = lean_st_ref_set(x_8, x_60, x_39);
lean_dec(x_8);
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
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_32);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_65 = lean_ctor_get(x_31, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_31, 1);
lean_inc(x_66);
lean_dec(x_31);
x_67 = lean_st_ref_get(x_8, x_66);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_st_ref_take(x_8, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = !lean_is_exclusive(x_70);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_70, 3);
lean_dec(x_74);
x_75 = !lean_is_exclusive(x_71);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_20);
x_76 = lean_st_ref_set(x_8, x_70, x_72);
lean_dec(x_8);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
lean_ctor_set_tag(x_76, 1);
lean_ctor_set(x_76, 0, x_65);
return x_76;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_65);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_71, 0);
lean_inc(x_81);
lean_dec(x_71);
x_82 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_20);
lean_ctor_set(x_70, 3, x_82);
x_83 = lean_st_ref_set(x_8, x_70, x_72);
lean_dec(x_8);
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
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
 lean_ctor_set_tag(x_86, 1);
}
lean_ctor_set(x_86, 0, x_65);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_87 = lean_ctor_get(x_70, 0);
x_88 = lean_ctor_get(x_70, 1);
x_89 = lean_ctor_get(x_70, 2);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_70);
x_90 = lean_ctor_get(x_71, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 x_91 = x_71;
} else {
 lean_dec_ref(x_71);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 1, 1);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_20);
x_93 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_88);
lean_ctor_set(x_93, 2, x_89);
lean_ctor_set(x_93, 3, x_92);
x_94 = lean_st_ref_set(x_8, x_93, x_72);
lean_dec(x_8);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
 lean_ctor_set_tag(x_97, 1);
}
lean_ctor_set(x_97, 0, x_65);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_23, 0);
lean_inc(x_98);
lean_dec(x_23);
x_99 = 0;
x_100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_99);
lean_ctor_set(x_22, 3, x_100);
x_101 = lean_st_ref_set(x_8, x_22, x_24);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
lean_inc(x_8);
x_103 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__1___rarg(x_13, x_5, x_6, x_7, x_8, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_st_ref_get(x_8, x_105);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_st_ref_take(x_8, x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_109, 3);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_109, 2);
lean_inc(x_114);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 lean_ctor_release(x_109, 2);
 lean_ctor_release(x_109, 3);
 x_115 = x_109;
} else {
 lean_dec_ref(x_109);
 x_115 = lean_box(0);
}
x_116 = lean_ctor_get(x_110, 0);
lean_inc(x_116);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_117 = x_110;
} else {
 lean_dec_ref(x_110);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 1, 1);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set_uint8(x_118, sizeof(void*)*1, x_20);
if (lean_is_scalar(x_115)) {
 x_119 = lean_alloc_ctor(0, 4, 0);
} else {
 x_119 = x_115;
}
lean_ctor_set(x_119, 0, x_112);
lean_ctor_set(x_119, 1, x_113);
lean_ctor_set(x_119, 2, x_114);
lean_ctor_set(x_119, 3, x_118);
x_120 = lean_st_ref_set(x_8, x_119, x_111);
lean_dec(x_8);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_104);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_124 = lean_ctor_get(x_103, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_103, 1);
lean_inc(x_125);
lean_dec(x_103);
x_126 = lean_st_ref_get(x_8, x_125);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
x_128 = lean_st_ref_take(x_8, x_127);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_129, 3);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_129, 2);
lean_inc(x_134);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 lean_ctor_release(x_129, 2);
 lean_ctor_release(x_129, 3);
 x_135 = x_129;
} else {
 lean_dec_ref(x_129);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_130, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_137 = x_130;
} else {
 lean_dec_ref(x_130);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 1, 1);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set_uint8(x_138, sizeof(void*)*1, x_20);
if (lean_is_scalar(x_135)) {
 x_139 = lean_alloc_ctor(0, 4, 0);
} else {
 x_139 = x_135;
}
lean_ctor_set(x_139, 0, x_132);
lean_ctor_set(x_139, 1, x_133);
lean_ctor_set(x_139, 2, x_134);
lean_ctor_set(x_139, 3, x_138);
x_140 = lean_st_ref_set(x_8, x_139, x_131);
lean_dec(x_8);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_142 = x_140;
} else {
 lean_dec_ref(x_140);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
 lean_ctor_set_tag(x_143, 1);
}
lean_ctor_set(x_143, 0, x_124);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_144 = lean_ctor_get(x_22, 0);
x_145 = lean_ctor_get(x_22, 1);
x_146 = lean_ctor_get(x_22, 2);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_22);
x_147 = lean_ctor_get(x_23, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_148 = x_23;
} else {
 lean_dec_ref(x_23);
 x_148 = lean_box(0);
}
x_149 = 0;
if (lean_is_scalar(x_148)) {
 x_150 = lean_alloc_ctor(0, 1, 1);
} else {
 x_150 = x_148;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set_uint8(x_150, sizeof(void*)*1, x_149);
x_151 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_151, 0, x_144);
lean_ctor_set(x_151, 1, x_145);
lean_ctor_set(x_151, 2, x_146);
lean_ctor_set(x_151, 3, x_150);
x_152 = lean_st_ref_set(x_8, x_151, x_24);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
lean_inc(x_8);
x_154 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__1___rarg(x_13, x_5, x_6, x_7, x_8, x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_st_ref_get(x_8, x_156);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_159 = lean_st_ref_take(x_8, x_158);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_160, 3);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
lean_dec(x_159);
x_163 = lean_ctor_get(x_160, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 2);
lean_inc(x_165);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 x_166 = x_160;
} else {
 lean_dec_ref(x_160);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_161, 0);
lean_inc(x_167);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_168 = x_161;
} else {
 lean_dec_ref(x_161);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(0, 1, 1);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set_uint8(x_169, sizeof(void*)*1, x_20);
if (lean_is_scalar(x_166)) {
 x_170 = lean_alloc_ctor(0, 4, 0);
} else {
 x_170 = x_166;
}
lean_ctor_set(x_170, 0, x_163);
lean_ctor_set(x_170, 1, x_164);
lean_ctor_set(x_170, 2, x_165);
lean_ctor_set(x_170, 3, x_169);
x_171 = lean_st_ref_set(x_8, x_170, x_162);
lean_dec(x_8);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_173 = x_171;
} else {
 lean_dec_ref(x_171);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_155);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_175 = lean_ctor_get(x_154, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_154, 1);
lean_inc(x_176);
lean_dec(x_154);
x_177 = lean_st_ref_get(x_8, x_176);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
x_179 = lean_st_ref_take(x_8, x_178);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_180, 3);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
lean_dec(x_179);
x_183 = lean_ctor_get(x_180, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_180, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_180, 2);
lean_inc(x_185);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 lean_ctor_release(x_180, 2);
 lean_ctor_release(x_180, 3);
 x_186 = x_180;
} else {
 lean_dec_ref(x_180);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_181, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 x_188 = x_181;
} else {
 lean_dec_ref(x_181);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(0, 1, 1);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set_uint8(x_189, sizeof(void*)*1, x_20);
if (lean_is_scalar(x_186)) {
 x_190 = lean_alloc_ctor(0, 4, 0);
} else {
 x_190 = x_186;
}
lean_ctor_set(x_190, 0, x_183);
lean_ctor_set(x_190, 1, x_184);
lean_ctor_set(x_190, 2, x_185);
lean_ctor_set(x_190, 3, x_189);
x_191 = lean_st_ref_set(x_8, x_190, x_182);
lean_dec(x_8);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_193 = x_191;
} else {
 lean_dec_ref(x_191);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
 lean_ctor_set_tag(x_194, 1);
}
lean_ctor_set(x_194, 0, x_175);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_195 = lean_ctor_get(x_7, 3);
lean_inc(x_195);
x_196 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__6___rarg(x_8, x_15);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_199 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__1___rarg(x_13, x_5, x_6, x_7, x_8, x_198);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__7(x_197, x_11, x_195, x_5, x_6, x_7, x_8, x_201);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_202, 0);
lean_dec(x_204);
lean_ctor_set(x_202, 0, x_200);
return x_202;
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_dec(x_202);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_200);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_207 = lean_ctor_get(x_199, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_199, 1);
lean_inc(x_208);
lean_dec(x_199);
x_209 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponedStep___spec__7(x_197, x_11, x_195, x_5, x_6, x_7, x_8, x_208);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_209, 0);
lean_dec(x_211);
lean_ctor_set_tag(x_209, 1);
lean_ctor_set(x_209, 0, x_207);
return x_209;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
lean_dec(x_209);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_207);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelOne;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabStateRefT___lambda__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("STWorld");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("StateRefT'");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_11 = l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__1;
x_12 = l_Lean_Meta_mkArrow(x_11, x_11, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__2;
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_17 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Elab_Term_elabTerm(x_2, x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__3;
x_22 = 0;
x_23 = lean_box(0);
lean_inc(x_6);
x_24 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_21, x_22, x_23, x_6, x_7, x_8, x_9, x_20);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Syntax_mkApp___closed__1;
lean_inc(x_25);
x_28 = lean_array_push(x_27, x_25);
lean_inc(x_19);
x_29 = lean_array_push(x_28, x_19);
x_30 = l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__5;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_31 = l_Lean_Meta_mkAppM___at_Lean_Elab_Term_elabStateRefT___spec__1(x_30, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_34 = l_Lean_Elab_Term_mkInstMVar(x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Syntax_mkAntiquotNode___closed__9;
x_37 = lean_array_push(x_36, x_25);
x_38 = lean_array_push(x_37, x_1);
x_39 = lean_array_push(x_38, x_19);
x_40 = l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__7;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_41 = l_Lean_Meta_mkAppM___at_Lean_Elab_Term_elabStateRefT___spec__1(x_40, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_apply_8(x_15, x_42, x_4, x_5, x_6, x_7, x_8, x_9, x_43);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_34);
if (x_49 == 0)
{
return x_34;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_34, 0);
x_51 = lean_ctor_get(x_34, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_34);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_31);
if (x_53 == 0)
{
return x_31;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_31, 0);
x_55 = lean_ctor_get(x_31, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_31);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_18);
if (x_57 == 0)
{
return x_18;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_18, 0);
x_59 = lean_ctor_get(x_18, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_18);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabStateRefT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Elab_Term_elabType(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_inc(x_16);
x_17 = l_Lean_Syntax_getKind(x_16);
x_18 = l_Lean_Parser_Term_macroDollarArg___elambda__1___closed__2;
x_19 = lean_name_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Term_elabStateRefT___lambda__2(x_13, x_16, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_Syntax_getArg(x_16, x_10);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = l_Lean_Elab_Term_elabStateRefT___lambda__2(x_13, x_22, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Lean_Meta_mkAppM___at_Lean_Elab_Term_elabStateRefT___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkAppM___at_Lean_Elab_Term_elabStateRefT___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabStateRefT___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabStateRefT___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabStateRefT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabStateRefT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabStateRefT___boxed), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabStateRefT(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_stateRefT___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Init_Data_ToString(lean_object*);
lean_object* initialize_Lean_Compiler_BorrowedAnnotation(lean_object*);
lean_object* initialize_Lean_Meta_KAbstract(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_BuiltinNotation(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_BorrowedAnnotation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_KAbstract(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabAnonymousCtor___closed__1 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__1);
l_Lean_Elab_Term_elabAnonymousCtor___closed__2 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__2);
l_Lean_Elab_Term_elabAnonymousCtor___closed__3 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__3);
l_Lean_Elab_Term_elabAnonymousCtor___closed__4 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__4);
l_Lean_Elab_Term_elabAnonymousCtor___closed__5 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__5);
l_Lean_Elab_Term_elabAnonymousCtor___closed__6 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__6);
l_Lean_Elab_Term_elabAnonymousCtor___closed__7 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__7);
l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabBorrowed___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabBorrowed___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabBorrowed___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabBorrowed(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandShow___closed__1 = _init_l_Lean_Elab_Term_expandShow___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__1);
l_Lean_Elab_Term_expandShow___closed__2 = _init_l_Lean_Elab_Term_expandShow___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__2);
l_Lean_Elab_Term_expandShow___closed__3 = _init_l_Lean_Elab_Term_expandShow___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__3);
l_Lean_Elab_Term_expandShow___closed__4 = _init_l_Lean_Elab_Term_expandShow___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandShow___closed__4);
l___regBuiltin_Lean_Elab_Term_expandShow___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandShow___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandShow___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandShow(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandHave___closed__1 = _init_l_Lean_Elab_Term_expandHave___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandHave___closed__1);
l_Lean_Elab_Term_expandHave___closed__2 = _init_l_Lean_Elab_Term_expandHave___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandHave___closed__2);
l___regBuiltin_Lean_Elab_Term_expandHave___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandHave___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandHave___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandHave(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_expandSuffices___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandSuffices___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandSuffices___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandSuffices(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__1 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__1);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__2 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__2);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__3 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__3);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__4 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__4);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__5 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__5);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__6 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__6);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__7 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__7();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__7);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__8 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__8();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__8);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__9 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__9();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__9);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__10 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__10();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__10);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__11 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__11();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__11);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__12 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__12();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__12);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__13 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__13();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__13);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__15 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__15();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__15);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__17 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__17();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__17);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__18 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__18();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__18);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__19 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__19();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__19);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__21 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__21();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__21);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__24 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__24();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__24);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__26 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__26();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__26);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__28 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__28();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__28);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__30 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__30();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__30);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__31 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__31();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__31);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__32 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__32();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__32);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__33 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__33();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__33);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__34 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__34();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__34);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__35 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__35();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__35);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__36 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__36();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__36);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__37 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__37();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__37);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__38 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__38();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__38);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__39 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__39();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__39);
l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__1 = _init_l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__1);
l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__2 = _init_l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabParserMacro___lambda__1___closed__2);
l_Lean_Elab_Term_elabParserMacro___closed__1 = _init_l_Lean_Elab_Term_elabParserMacro___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabParserMacro___closed__1);
l___regBuiltin_Lean_Elab_Term_elabParserMacro___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabParserMacro___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabParserMacro___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabParserMacro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__1 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__1);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__2 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__2);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__3 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__3);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__4 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__4);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__5 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__5);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__6 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__6);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__7 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__7();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__7);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__8 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__8();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__8);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__9 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__9();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__9);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__10 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__10();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__10);
l_Lean_Elab_Term_elabTParserMacro___closed__1 = _init_l_Lean_Elab_Term_elabTParserMacro___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabTParserMacro___closed__1);
l___regBuiltin_Lean_Elab_Term_elabTParserMacro___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabTParserMacro___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTParserMacro___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabTParserMacro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__1 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__1);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__2 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_mkNativeReflAuxDecl___closed__2);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__1 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__1);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__2 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___lambda__1___closed__2);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__1 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__1);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__2 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabClosedTerm___closed__2);
l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__1 = _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__1);
l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__2 = _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__2);
l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__3 = _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__3);
l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__4 = _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__4);
l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__5 = _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__5);
l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__6 = _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__6);
l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__7 = _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__7);
l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__8 = _init_l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___lambda__1___closed__8);
l_Lean_Elab_Term_elabNativeRefl___closed__1 = _init_l_Lean_Elab_Term_elabNativeRefl___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___closed__1);
l_Lean_Elab_Term_elabNativeRefl___closed__2 = _init_l_Lean_Elab_Term_elabNativeRefl___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeRefl___closed__2);
l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNativeRefl___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabNativeRefl(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__1 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__1);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__2 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__2);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__3 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__3();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__3);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__4 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__4();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__4);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__5 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__5();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_getPropToDecide___closed__5);
l_Lean_Elab_Term_elabNativeDecide___rarg___closed__1 = _init_l_Lean_Elab_Term_elabNativeDecide___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabNativeDecide___rarg___closed__1);
l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNativeDecide___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabNativeDecide(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabDecide___rarg___closed__1 = _init_l_Lean_Elab_Term_elabDecide___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabDecide___rarg___closed__1);
l___regBuiltin_Lean_Elab_Term_elabDecide___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabDecide___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabDecide___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabDecide(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabPanic___closed__1 = _init_l_Lean_Elab_Term_elabPanic___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__1);
l_Lean_Elab_Term_elabPanic___closed__2 = _init_l_Lean_Elab_Term_elabPanic___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__2);
l_Lean_Elab_Term_elabPanic___closed__3 = _init_l_Lean_Elab_Term_elabPanic___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__3);
l_Lean_Elab_Term_elabPanic___closed__4 = _init_l_Lean_Elab_Term_elabPanic___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__4);
l_Lean_Elab_Term_elabPanic___closed__5 = _init_l_Lean_Elab_Term_elabPanic___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__5);
l_Lean_Elab_Term_elabPanic___closed__6 = _init_l_Lean_Elab_Term_elabPanic___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__6);
l_Lean_Elab_Term_elabPanic___closed__7 = _init_l_Lean_Elab_Term_elabPanic___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__7);
l_Lean_Elab_Term_elabPanic___closed__8 = _init_l_Lean_Elab_Term_elabPanic___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__8);
l_Lean_Elab_Term_elabPanic___closed__9 = _init_l_Lean_Elab_Term_elabPanic___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__9);
l_Lean_Elab_Term_elabPanic___closed__10 = _init_l_Lean_Elab_Term_elabPanic___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__10);
l_Lean_Elab_Term_elabPanic___closed__11 = _init_l_Lean_Elab_Term_elabPanic___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__11);
l_Lean_Elab_Term_elabPanic___closed__12 = _init_l_Lean_Elab_Term_elabPanic___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_elabPanic___closed__12);
l___regBuiltin_Lean_Elab_Term_elabPanic___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabPanic___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabPanic___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabPanic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandUnreachable___rarg___closed__1 = _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandUnreachable___rarg___closed__1);
l_Lean_Elab_Term_expandUnreachable___rarg___closed__2 = _init_l_Lean_Elab_Term_expandUnreachable___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandUnreachable___rarg___closed__2);
l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandUnreachable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandAssert___closed__1 = _init_l_Lean_Elab_Term_expandAssert___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__1);
l_Lean_Elab_Term_expandAssert___closed__2 = _init_l_Lean_Elab_Term_expandAssert___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__2);
l_Lean_Elab_Term_expandAssert___closed__3 = _init_l_Lean_Elab_Term_expandAssert___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__3);
l_Lean_Elab_Term_expandAssert___closed__4 = _init_l_Lean_Elab_Term_expandAssert___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandAssert___closed__4);
l___regBuiltin_Lean_Elab_Term_expandAssert___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandAssert___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandAssert___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandAssert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandDbgTrace___closed__1 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__1);
l_Lean_Elab_Term_expandDbgTrace___closed__2 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__2);
l_Lean_Elab_Term_expandDbgTrace___closed__3 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__3);
l_Lean_Elab_Term_expandDbgTrace___closed__4 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__4);
l_Lean_Elab_Term_expandDbgTrace___closed__5 = _init_l_Lean_Elab_Term_expandDbgTrace___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandDbgTrace___closed__5);
l___regBuiltin_Lean_Elab_Term_expandDbgTrace___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandDbgTrace___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandDbgTrace___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandDbgTrace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandSorry___rarg___closed__1 = _init_l_Lean_Elab_Term_expandSorry___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandSorry___rarg___closed__1);
l_Lean_Elab_Term_expandSorry___rarg___closed__2 = _init_l_Lean_Elab_Term_expandSorry___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandSorry___rarg___closed__2);
l_Lean_Elab_Term_expandSorry___rarg___closed__3 = _init_l_Lean_Elab_Term_expandSorry___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandSorry___rarg___closed__3);
l_Lean_Elab_Term_expandSorry___rarg___closed__4 = _init_l_Lean_Elab_Term_expandSorry___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandSorry___rarg___closed__4);
l_Lean_Elab_Term_expandSorry___rarg___closed__5 = _init_l_Lean_Elab_Term_expandSorry___rarg___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandSorry___rarg___closed__5);
l_Lean_Elab_Term_expandSorry___rarg___closed__6 = _init_l_Lean_Elab_Term_expandSorry___rarg___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandSorry___rarg___closed__6);
l_Lean_Elab_Term_expandSorry___rarg___closed__7 = _init_l_Lean_Elab_Term_expandSorry___rarg___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_expandSorry___rarg___closed__7);
l_Lean_Elab_Term_expandSorry___rarg___closed__8 = _init_l_Lean_Elab_Term_expandSorry___rarg___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_expandSorry___rarg___closed__8);
l___regBuiltin_Lean_Elab_Term_expandSorry___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandSorry___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandSorry___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandSorry(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandEmptyC___closed__1 = _init_l_Lean_Elab_Term_expandEmptyC___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandEmptyC___closed__1);
l_Lean_Elab_Term_expandEmptyC___closed__2 = _init_l_Lean_Elab_Term_expandEmptyC___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandEmptyC___closed__2);
l_Lean_Elab_Term_expandEmptyC___closed__3 = _init_l_Lean_Elab_Term_expandEmptyC___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandEmptyC___closed__3);
l_Lean_Elab_Term_expandEmptyC___closed__4 = _init_l_Lean_Elab_Term_expandEmptyC___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandEmptyC___closed__4);
l_Lean_Elab_Term_expandEmptyC___closed__5 = _init_l_Lean_Elab_Term_expandEmptyC___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandEmptyC___closed__5);
l_Lean_Elab_Term_expandEmptyC___closed__6 = _init_l_Lean_Elab_Term_expandEmptyC___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandEmptyC___closed__6);
l_Lean_Elab_Term_expandEmptyC___closed__7 = _init_l_Lean_Elab_Term_expandEmptyC___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_expandEmptyC___closed__7);
l_Lean_Elab_Term_expandEmptyC___closed__8 = _init_l_Lean_Elab_Term_expandEmptyC___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_expandEmptyC___closed__8);
l_Lean_Elab_Term_expandEmptyC___closed__9 = _init_l_Lean_Elab_Term_expandEmptyC___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_expandEmptyC___closed__9);
l___regBuiltin_Lean_Elab_Term_expandEmptyC___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandEmptyC___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandEmptyC___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandEmptyC(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_mkPairs_loop___closed__1 = _init_l_Lean_Elab_Term_mkPairs_loop___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkPairs_loop___closed__1);
l_Lean_Elab_Term_mkPairs_loop___closed__2 = _init_l_Lean_Elab_Term_mkPairs_loop___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkPairs_loop___closed__2);
l_Lean_Elab_Term_mkPairs_loop___closed__3 = _init_l_Lean_Elab_Term_mkPairs_loop___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_mkPairs_loop___closed__3);
l_Lean_Elab_Term_mkPairs_loop___closed__4 = _init_l_Lean_Elab_Term_mkPairs_loop___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_mkPairs_loop___closed__4);
l_Lean_Elab_Term_mkPairs_loop___closed__5 = _init_l_Lean_Elab_Term_mkPairs_loop___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_mkPairs_loop___closed__5);
l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___boxed__const__1 = _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___boxed__const__1);
l_Lean_Elab_Term_elabParen___closed__1 = _init_l_Lean_Elab_Term_elabParen___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__1);
l_Lean_Elab_Term_elabParen___closed__2 = _init_l_Lean_Elab_Term_elabParen___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__2);
l_Lean_Elab_Term_elabParen___closed__3 = _init_l_Lean_Elab_Term_elabParen___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__3);
l___regBuiltin_Lean_Elab_Term_elabParen___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabParen___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabParen___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabParen(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabSubst___closed__1 = _init_l_Lean_Elab_Term_elabSubst___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabSubst___closed__1);
l_Lean_Elab_Term_elabSubst___closed__2 = _init_l_Lean_Elab_Term_elabSubst___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabSubst___closed__2);
l_Lean_Elab_Term_elabSubst___closed__3 = _init_l_Lean_Elab_Term_elabSubst___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabSubst___closed__3);
l_Lean_Elab_Term_elabSubst___closed__4 = _init_l_Lean_Elab_Term_elabSubst___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabSubst___closed__4);
l_Lean_Elab_Term_elabSubst___closed__5 = _init_l_Lean_Elab_Term_elabSubst___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabSubst___closed__5);
l_Lean_Elab_Term_elabSubst___closed__6 = _init_l_Lean_Elab_Term_elabSubst___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabSubst___closed__6);
l_Lean_Elab_Term_elabSubst___closed__7 = _init_l_Lean_Elab_Term_elabSubst___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_elabSubst___closed__7);
l_Lean_Elab_Term_elabSubst___closed__8 = _init_l_Lean_Elab_Term_elabSubst___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_elabSubst___closed__8);
l_Lean_Elab_Term_elabSubst___closed__9 = _init_l_Lean_Elab_Term_elabSubst___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_elabSubst___closed__9);
l___regBuiltin_Lean_Elab_Term_elabSubst___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabSubst___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSubst___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabSubst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__1 = _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__1);
l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__2 = _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__2);
l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__3 = _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__3);
l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__4 = _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__4);
l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__5 = _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__5);
l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__6 = _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__6);
l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__7 = _init_l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__7);
l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabStateRefT(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
