// Lean compiler output
// Module: Lean.Elab.BuiltinNotation
// Imports: Init Init.Data.ToString Lean.Compiler.BorrowedAnnotation Lean.Meta.KAbstract Lean.Meta.Transform Lean.Elab.Term Lean.Elab.SyntheticMVars
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
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Term_elabAnonymousCtor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__26;
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__4;
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg___closed__2;
lean_object* l_Lean_Elab_Term_mkPairs_loop___closed__5;
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_instReprOption___rarg___closed__1;
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(lean_object*);
extern lean_object* l_instReprSigma___rarg___closed__2;
lean_object* l_Lean_Elab_Term_expandSuffices___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__4;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__36;
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__2;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16009____closed__5;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_Term_expandCDot_x3f_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__1;
lean_object* l_Lean_Elab_Term_elabSubst_match__1___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandAssert___closed__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__31;
lean_object* l_Lean_Elab_Term_expandHave___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getDeclName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__2;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__1;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabParen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSorry___closed__11;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__3;
lean_object* l_Lean_Elab_Term_elabSorry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_myMacro____x40_Init_NotationExtra___hyg_5198____spec__3(size_t, size_t, lean_object*);
extern lean_object* l_Lean_Parser_Term_subst___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_unreachable___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__1(lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_935____closed__4;
lean_object* l_Lean_Elab_Term_elabSorry___closed__10;
extern lean_object* l_Lean_Parser_Term_anonymousCtor___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__12;
extern lean_object* l_Lean_Parser_Tactic_tacticHave_____closed__5;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Elab_Term_elabLeadingParserMacro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAssert_match__1(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__8;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__19;
extern lean_object* l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__5;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__3;
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_23____closed__7;
lean_object* l___regBuiltin_Lean_Elab_Term_elabNoindex(lean_object*);
lean_object* l_Lean_Elab_Term_elabSorry___closed__7;
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16009____closed__6;
extern lean_object* l_instReprBool___closed__1;
lean_object* l_Lean_Elab_Term_expandHave___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_termS_x21_____closed__3;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandAssert___closed__2;
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__1;
extern lean_object* l_Lean_Parser_Term_leading__parser___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___closed__5;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__1;
extern lean_object* l_termDepIfThenElse___closed__24;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__11;
extern lean_object* l_Lean_interpolatedStrKind;
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryPureCoe_x3f___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabSubst___closed__1;
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__9;
lean_object* l_Lean_Elab_Term_mkPairs_loop___closed__2;
lean_object* l_Lean_Elab_Term_elabSubst___closed__7;
lean_object* l_Lean_Elab_Term_elabPanic___closed__6;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabParen(lean_object*);
lean_object* l_Lean_Elab_Term_expandDbgTrace___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkPairs_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabSorry(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__9;
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__1;
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__4;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTrailingParserMacro___closed__1;
extern lean_object* l_Lean_Meta_assert___closed__1;
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_Lean_Parser_Term_tupleTail___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__35;
extern lean_object* l_Lean_Parser_Term_noindex___elambda__1___closed__2;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__6;
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__4;
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__2;
lean_object* l_Lean_Elab_Term_expandShow___closed__1;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_myMacro____x40_Init_Notation___hyg_16227__expandListLit___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__18;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__30;
extern lean_object* l_termS_x21_____closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandShow___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16;
lean_object* l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAssert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___closed__3;
lean_object* l_Lean_Elab_Term_mkPairs_loop___closed__4;
lean_object* l_Lean_Elab_Term_elabParen___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__7;
lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation(lean_object*);
lean_object* l_Lean_Elab_Term_elabParen___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabNoindex___closed__1;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandHave___lambda__1___closed__3;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__10;
lean_object* l_Lean_Elab_Term_expandHave___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandShow___closed__2;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAssert_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__24;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandHave(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13918____closed__9;
lean_object* l_Lean_Syntax_SepArray_getElems___rarg(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabPanic(lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__6;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20;
lean_object* l_Lean_Elab_Term_elabNoindex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_emptyC___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__3;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__10;
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__32;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_setOptionFromString___closed__4;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2204____closed__3;
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__3;
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__6;
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__5;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandHave___closed__1;
extern lean_object* l_Lean_numLitKind;
lean_object* l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandShow___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instQuoteProd___rarg___closed__2;
lean_object* l_Lean_Elab_Term_expandDbgTrace(lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14520____closed__14;
lean_object* l_Lean_Elab_Term_elabTrailingParserMacro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__3;
lean_object* l_Lean_Elab_Term_mkPairs_loop___closed__1;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__5;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandHave_match__1(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabStateRefT___closed__1;
extern lean_object* l_Lean_Parser_Term_macroDollarArg___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandUnreachable(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
lean_object* l_Lean_Elab_log___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16009____closed__3;
lean_object* l___regBuiltin_Lean_Elab_Term_expandEmptyC___closed__1;
extern lean_object* l_Lean_Meta_mkArrow___closed__2;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__5;
lean_object* l_Lean_Elab_Term_expandHave___lambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_notFollowedByRedefinedTermToken___elambda__1___closed__43;
lean_object* l_Lean_Elab_getRefPosition___at_Lean_Elab_Term_elabPanic___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__4;
lean_object* l_Lean_Elab_Term_expandHave___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__2(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13918____closed__8;
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Term_expandSuffices(lean_object*);
lean_object* l_Lean_Elab_Term_elabNoindex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__5;
lean_object* l_Lean_Elab_Term_elabSubst_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_mkPairs_loop___closed__3;
lean_object* l_Lean_Elab_Term_expandDbgTrace___closed__3;
extern lean_object* l_Lean_strLitKind___closed__2;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__8;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instQuoteBool___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__7;
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux_match__1(lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabParen___closed__1;
lean_object* l_Lean_Elab_Term_elabLeadingParserMacro___closed__1;
lean_object* l_Lean_Elab_Term_elabParen___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_maxPrec;
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_19733____closed__1;
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Term_elabAnonymousCtor___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__2;
lean_object* l_Lean_Elab_Term_elabSorry___closed__2;
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__9;
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_19733____closed__2;
lean_object* l_Lean_Elab_Term_expandShow(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__21;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__3;
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_19931____closed__2;
lean_object* l___private_Init_Meta_0__Lean_quoteName(lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTrailingParserMacro___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1___closed__1;
extern lean_object* l_Lean_instInhabitedExpr;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13918____closed__12;
lean_object* l_Lean_Elab_Term_elabTrailingParserMacro___lambda__1___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16009____closed__11;
extern lean_object* l_Lean_instToExprUnit___lambda__1___closed__3;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandDbgTrace___closed__1;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst_match__1(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__6;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15440____closed__8;
lean_object* l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
lean_object* l_Lean_Elab_Term_elabTrailingParserMacro___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_22292____closed__1;
extern lean_object* l_Lean_instInhabitedSyntax;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_22292____closed__2;
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_elabAnonymousCtor___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_dbgTrace___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_elabSubst___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSuffices___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__11;
lean_object* l___regBuiltin_Lean_Elab_Term_elabBorrowed(lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15440____closed__9;
lean_object* l_Lean_Elab_Term_expandAssert___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__4;
lean_object* l___regBuiltin_Lean_Elab_Term_expandEmptyC(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14520____closed__13;
extern lean_object* l_Lean_KernelException_toMessageData___closed__3;
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_19537____closed__3;
extern lean_object* l_Lean_Syntax_mkAntiquotNode___closed__9;
extern lean_object* l_term___x2b_x2b_____closed__2;
lean_object* l_Lean_Elab_Term_expandHave___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabSorry___closed__1;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__10;
extern lean_object* l_Lean_Parser_Term_cdot___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabSubst___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_17914____closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29;
lean_object* l___regBuiltin_Lean_Elab_Term_elabTrailingParserMacro(lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__7;
lean_object* l_Lean_Elab_Term_expandSuffices___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSuffices___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
uint8_t l_List_beq___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandHave___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__2(lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_22292____closed__3;
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_23____closed__13;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_dbgTrace___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25;
lean_object* l_Lean_Elab_Term_expandHave(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot___boxed(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16009____closed__12;
extern lean_object* l_Lean_Syntax_mkApp___closed__1;
lean_object* l_Lean_Elab_Term_elabPanic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSuffices___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__3;
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__3;
lean_object* l_Lean_Elab_Term_elabSorry___closed__1;
lean_object* l_Lean_Elab_Term_elabTrailingParserMacro___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__7;
lean_object* l___regBuiltin_Lean_Elab_Term_expandShow(lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* lean_environment_main_module(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__5;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__28;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14;
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__3;
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSorry___closed__8;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabAnonymousCtor___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__5;
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__2___closed__5;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Elab_Term_elabSubst___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_NotationExtra___hyg_5198____closed__6;
lean_object* l_Lean_Elab_Term_expandEmptyC___closed__7;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
extern lean_object* l_Lean_Parser_Term_sufficesDecl___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_appendCore___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStateRefT___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_23____closed__8;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__37;
lean_object* l___regBuiltin_Lean_Elab_Term_elabSubst(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___boxed__const__1;
lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Term_elabAnonymousCtor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_adaptExpander___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSorry___closed__5;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__15;
lean_object* l_Lean_Elab_Term_elabSorry___closed__3;
lean_object* l_Lean_Elab_Term_elabPanic___closed__12;
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot___spec__1(lean_object*, size_t, size_t);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_expandInterpolatedStr___lambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_panic___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__17;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandHave___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_borrowed___elambda__1___closed__2;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__2;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_getConstInfoCtor___rarg___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabPanic___closed__8;
extern lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7;
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_case___closed__7;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabLeadingParserMacro(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__9;
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSuffices___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___closed__4;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__4;
lean_object* l_Lean_Elab_Term_elabTrailingParserMacro___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___closed__9;
lean_object* l_Lean_Elab_Term_elabPanic___closed__9;
extern lean_object* l_termIfThenElse___closed__2;
lean_object* l_Lean_Elab_Term_elabPanic___closed__1;
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_let__fun___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabTrailingParserMacro___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandUnreachable___boxed(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__5;
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__2;
lean_object* l_Lean_Elab_Term_elabSorry___closed__9;
extern lean_object* l_Lean_Parser_Term_let__fun___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_mkPairs___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_prec_x28___x29___closed__7;
lean_object* l_Lean_Elab_Term_elabSubst___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabTrailingParserMacro___closed__1;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__8;
lean_object* l_Lean_Elab_Term_mkPairs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__5;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot_match__1(lean_object*);
extern lean_object* l_prec_x28___x29___closed__3;
lean_object* l_Lean_Elab_Term_elabStateRefT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_trailing__parser___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_mkPairs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandUnreachable___rarg___closed__1;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__6;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandSuffices(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Elab_Term_expandAssert___closed__3;
lean_object* l_Lean_Elab_Term_expandSuffices___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandUnreachable(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__4;
extern lean_object* l_Lean_Parser_Tactic_intro___closed__1;
lean_object* l_Lean_Elab_Term_elabTrailingParserMacro___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_17279____closed__3;
lean_object* l_Lean_Elab_Term_elabSubst___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_beq___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSorry___closed__4;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___closed__8;
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_19537____closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__13;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___closed__7;
extern lean_object* l_Lean_expandExplicitBindersAux_loop___closed__4;
extern lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16009____closed__4;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandSuffices___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_expandEmptyC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__1;
lean_object* l_Lean_Elab_Term_expandHave_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfHasMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSorry___closed__6;
lean_object* l_Lean_Elab_Term_elabBorrowed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13918____closed__10;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Term_elabPanic___closed__1;
extern lean_object* l_Lean_levelOne;
uint8_t l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_hasCDot(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSubst___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandAssert(lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__2;
lean_object* l_Lean_Elab_Term_elabSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandDbgTrace(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_elabAnonymousCtor___spec__4(lean_object*);
lean_object* l_Lean_Elab_getRefPosition___at_Lean_Elab_Term_elabPanic___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__33;
lean_object* l___regBuiltin_Lean_Elab_Term_elabBorrowed___closed__1;
extern lean_object* l_instReprSigma___rarg___closed__6;
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandHave___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabStateRefT(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__4;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabAnonymousCtor___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandAssert___closed__1;
lean_object* l_Lean_Elab_Term_elabSubst_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabLeadingParserMacro___closed__1;
lean_object* l_Lean_Elab_Term_elabSubst___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Term_elabAnonymousCtor___closed__1;
extern lean_object* l_Lean_Meta_mkSorry___closed__2;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__3___rarg(lean_object*);
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__34;
lean_object* l_Lean_Syntax_reprint(lean_object*);
lean_object* l_Lean_Elab_Term_expandCDot_x3f_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
extern lean_object* l_Lean_Parser_Term_stateRefT___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabAnonymousCtor_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabPanic___closed__4;
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_935____closed__3;
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__2;
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__8;
lean_object* l_Lean_Elab_Term_expandAssert___closed__2;
lean_object* l_Lean_Elab_Term_elabSubst___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandCDot_x3f(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkSorry___closed__1;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_expandExplicitBindersAux_loop___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Term_expandUnreachable___closed__1;
lean_object* l_Lean_markBorrowed(lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Term_elabAnonymousCtor___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabAnonymousCtor___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Term_elabAnonymousCtor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 6)
{
uint8_t x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = l_Lean_mkConst(x_1, x_18);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_KernelException_toMessageData___closed__3;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_getConstInfoCtor___rarg___lambda__1___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Elab_Term_elabAnonymousCtor___spec__2(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
return x_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Term_elabAnonymousCtor___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_nat_dec_le(x_13, x_4);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_3, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_3, x_17);
lean_dec(x_3);
x_19 = l_Lean_instInhabitedExpr;
x_20 = lean_array_get(x_19, x_1, x_4);
lean_inc(x_8);
x_21 = l_Lean_Meta_getFVarLocalDecl(x_20, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_LocalDecl_binderInfo(x_22);
lean_dec(x_22);
x_25 = l_Lean_BinderInfo_isExplicit(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_2, 2);
x_27 = lean_nat_add(x_4, x_26);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_27;
x_12 = x_23;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_30 = lean_ctor_get(x_2, 2);
x_31 = lean_nat_add(x_4, x_30);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_31;
x_5 = x_29;
x_12 = x_23;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_21, 0);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_21);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
}
else
{
lean_object* x_38; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_12);
return x_38;
}
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_elabAnonymousCtor___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryPureCoe_x3f___spec__1___rarg___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
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
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_elabAnonymousCtor___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_elabAnonymousCtor___spec__4___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_array_get_size(x_2);
x_13 = lean_unsigned_to_nat(1u);
lean_inc(x_12);
lean_inc(x_11);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Std_Range_forIn_loop___at_Lean_Elab_Term_elabAnonymousCtor___spec__3(x_2, x_14, x_12, x_11, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
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
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
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
}
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_3);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_2);
x_12 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_3, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid constructor ⟨...⟩, insufficient number of arguments, constructs '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not have explicit fields, but #");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" provided");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_3);
x_17 = lean_nat_dec_eq(x_16, x_4);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_4, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_4, x_20);
lean_inc(x_21);
lean_inc(x_3);
x_22 = l_Array_toSubarray___rarg(x_3, x_21, x_16);
x_23 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_13, x_14, x_15);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Term_getCurrMacroScope(x_9, x_10, x_11, x_12, x_13, x_14, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Elab_Term_getMainModule___rarg(x_14, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_instReprSigma___rarg___closed__2;
lean_inc(x_24);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Array_empty___closed__1;
x_33 = lean_array_push(x_32, x_31);
x_34 = l_Array_ofSubarray___rarg(x_22);
lean_dec(x_22);
x_35 = lean_array_get_size(x_34);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = 0;
x_38 = x_34;
x_39 = l_Array_mapMUnsafe_map___at_myMacro____x40_Init_NotationExtra___hyg_5198____spec__3(x_36, x_37, x_38);
x_40 = x_39;
x_41 = l_myMacro____x40_Init_NotationExtra___hyg_5198____closed__6;
x_42 = l_Lean_mkSepArray(x_40, x_41);
lean_dec(x_40);
x_43 = l_Array_appendCore___rarg(x_32, x_42);
lean_dec(x_42);
x_44 = l_Lean_nullKind___closed__2;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_array_push(x_33, x_45);
x_47 = l_instReprSigma___rarg___closed__6;
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_24);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_array_push(x_46, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_5);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Array_toSubarray___rarg(x_3, x_18, x_21);
x_52 = l_Array_ofSubarray___rarg(x_51);
lean_dec(x_51);
x_53 = lean_array_push(x_52, x_50);
x_54 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_13, x_14, x_29);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lean_Elab_Term_getCurrMacroScope(x_9, x_10, x_11, x_12, x_13, x_14, x_55);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = l_Lean_Elab_Term_getMainModule___rarg(x_14, x_57);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_myMacro____x40_Init_Notation___hyg_2204____closed__3;
x_61 = lean_name_mk_string(x_6, x_60);
x_62 = l_Lean_mkCIdentFrom(x_1, x_7);
x_63 = lean_array_push(x_32, x_62);
x_64 = l_Array_appendCore___rarg(x_32, x_53);
lean_dec(x_53);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_44);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_array_push(x_63, x_65);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Elab_Term_elabAnonymousCtor___lambda__2(x_1, x_2, x_67, x_9, x_10, x_11, x_12, x_13, x_14, x_59);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_69, 0, x_7);
x_70 = l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__2;
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__4;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_16);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__6;
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__4(x_78, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
return x_79;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_79);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_16);
lean_dec(x_5);
x_84 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_13, x_14, x_15);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = l_Lean_Elab_Term_getCurrMacroScope(x_9, x_10, x_11, x_12, x_13, x_14, x_85);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_Lean_Elab_Term_getMainModule___rarg(x_14, x_87);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = l_myMacro____x40_Init_Notation___hyg_2204____closed__3;
x_91 = lean_name_mk_string(x_6, x_90);
x_92 = l_Lean_mkCIdentFrom(x_1, x_7);
x_93 = l_Array_empty___closed__1;
x_94 = lean_array_push(x_93, x_92);
x_95 = l_Array_appendCore___rarg(x_93, x_3);
lean_dec(x_3);
x_96 = l_Lean_nullKind___closed__2;
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = lean_array_push(x_94, x_97);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_91);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_Elab_Term_elabAnonymousCtor___lambda__2(x_1, x_2, x_99, x_9, x_10, x_11, x_12, x_13, x_14, x_89);
return x_100;
}
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
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid constructor ⟨...⟩, expected type must be an inductive type ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabAnonymousCtor___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid constructor ⟨...⟩, expected type must be an inductive type with only one constructor ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabAnonymousCtor___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has #");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabAnonymousCtor___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" explicit fields, but only #");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabAnonymousCtor___closed__9;
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
x_18 = l_Lean_Elab_Term_elabAnonymousCtor___closed__2;
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
x_33 = l_Lean_Elab_Term_elabAnonymousCtor___closed__4;
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
x_42 = l_Lean_Elab_Term_elabAnonymousCtor___closed__6;
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
lean_object* x_48; lean_object* x_49; 
lean_dec(x_23);
x_48 = lean_ctor_get(x_40, 0);
lean_inc(x_48);
lean_dec(x_40);
lean_inc(x_3);
lean_inc(x_48);
x_49 = l_Lean_getConstInfoCtor___at_Lean_Elab_Term_elabAnonymousCtor___spec__1(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 2);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabAnonymousCtor___lambda__1___boxed), 10, 1);
lean_closure_set(x_54, 0, x_50);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_55 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_elabAnonymousCtor___spec__4___rarg(x_53, x_54, x_3, x_4, x_5, x_6, x_7, x_8, x_51);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Syntax_SepArray_getElems___rarg(x_15);
lean_dec(x_15);
x_59 = lean_array_get_size(x_58);
x_60 = lean_nat_dec_lt(x_59, x_56);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_59);
x_61 = l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
x_62 = lean_box(0);
x_63 = l_Lean_Elab_Term_elabAnonymousCtor___lambda__3(x_1, x_2, x_58, x_56, x_10, x_61, x_48, x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_57);
lean_dec(x_56);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_58);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_64, 0, x_48);
x_65 = l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__2;
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lean_Elab_Term_elabAnonymousCtor___closed__8;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_56);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Elab_Term_elabAnonymousCtor___closed__10;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_59);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__6;
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_78, x_3, x_4, x_5, x_6, x_7, x_8, x_57);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
return x_79;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_79);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_48);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_55);
if (x_84 == 0)
{
return x_55;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_55, 0);
x_86 = lean_ctor_get(x_55, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_55);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_48);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_49);
if (x_88 == 0)
{
return x_49;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_49, 0);
x_90 = lean_ctor_get(x_49, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_49);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_47);
lean_dec(x_40);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_92 = l_Lean_indentExpr(x_23);
x_93 = l_Lean_Elab_Term_elabAnonymousCtor___closed__6;
x_94 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = l_Lean_KernelException_toMessageData___closed__15;
x_96 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_96, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_38);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_98 = l_Lean_indentExpr(x_23);
x_99 = l_Lean_Elab_Term_elabAnonymousCtor___closed__4;
x_100 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = l_Lean_KernelException_toMessageData___closed__15;
x_102 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_102, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_104 = l_Lean_indentExpr(x_23);
x_105 = l_Lean_Elab_Term_elabAnonymousCtor___closed__4;
x_106 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = l_Lean_KernelException_toMessageData___closed__15;
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_108, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_109;
}
}
else
{
uint8_t x_110; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_22);
if (x_110 == 0)
{
return x_22;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_22, 0);
x_112 = lean_ctor_get(x_22, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_22);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_16);
if (x_114 == 0)
{
return x_16;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_16, 0);
x_116 = lean_ctor_get(x_16, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_16);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_elabAnonymousCtor___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Term_elabAnonymousCtor___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_getConstInfoCtor___at_Lean_Elab_Term_elabAnonymousCtor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfoCtor___at_Lean_Elab_Term_elabAnonymousCtor___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Term_elabAnonymousCtor___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Elab_Term_elabAnonymousCtor___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabAnonymousCtor___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Term_elabAnonymousCtor___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
lean_dec(x_4);
return x_16;
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
x_16 = l_Lean_Elab_Term_elabTerm(x_14, x_2, x_15, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_1 = lean_mk_string("this");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandShow___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandShow___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandShow(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__2;
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
x_12 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__4;
lean_inc(x_11);
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_1);
x_14 = l_myMacro____x40_Init_Notation___hyg_22292____closed__2;
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
x_19 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_17279____closed__3;
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
x_23 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_2, x_3);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__1;
lean_inc(x_25);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Array_empty___closed__1;
x_29 = lean_array_push(x_28, x_27);
x_30 = lean_array_push(x_29, x_9);
x_31 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__5;
lean_inc(x_25);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_array_push(x_28, x_32);
x_34 = l_myMacro____x40_Init_Notation___hyg_22292____closed__3;
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
x_45 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__1;
lean_inc(x_43);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Array_empty___closed__1;
x_48 = lean_array_push(x_47, x_46);
x_49 = lean_array_push(x_48, x_9);
x_50 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__5;
lean_inc(x_43);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_array_push(x_47, x_51);
x_53 = l_myMacro____x40_Init_Notation___hyg_22292____closed__3;
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
x_64 = l_Lean_Elab_Term_expandShow___closed__2;
x_65 = l_Lean_mkIdentFrom(x_1, x_64);
lean_dec(x_1);
x_66 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_2, x_3);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = l_Lean_Parser_Term_let__fun___elambda__1___closed__1;
lean_inc(x_68);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Array_empty___closed__1;
x_72 = lean_array_push(x_71, x_70);
lean_inc(x_65);
x_73 = lean_array_push(x_71, x_65);
x_74 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_75 = lean_array_push(x_73, x_74);
x_76 = l_myMacro____x40_Init_Notation___hyg_15440____closed__9;
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
x_86 = l_myMacro____x40_Init_Notation___hyg_16009____closed__11;
lean_inc(x_68);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_68);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_array_push(x_85, x_87);
x_89 = lean_array_push(x_88, x_63);
x_90 = l_myMacro____x40_Init_Notation___hyg_16009____closed__6;
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_array_push(x_71, x_91);
x_93 = l_myMacro____x40_Init_Notation___hyg_16009____closed__4;
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = lean_array_push(x_72, x_94);
x_96 = l_myMacro____x40_Init_Notation___hyg_16009____closed__12;
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_68);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_array_push(x_71, x_97);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_83);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_array_push(x_95, x_99);
x_101 = lean_array_push(x_100, x_65);
x_102 = l_Lean_Parser_Term_let__fun___elambda__1___closed__2;
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
x_106 = l_Lean_Parser_Term_let__fun___elambda__1___closed__1;
lean_inc(x_104);
x_107 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Array_empty___closed__1;
x_109 = lean_array_push(x_108, x_107);
lean_inc(x_65);
x_110 = lean_array_push(x_108, x_65);
x_111 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_112 = lean_array_push(x_110, x_111);
x_113 = l_myMacro____x40_Init_Notation___hyg_15440____closed__9;
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
x_123 = l_myMacro____x40_Init_Notation___hyg_16009____closed__11;
lean_inc(x_104);
x_124 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_124, 0, x_104);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_array_push(x_122, x_124);
x_126 = lean_array_push(x_125, x_63);
x_127 = l_myMacro____x40_Init_Notation___hyg_16009____closed__6;
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
x_129 = lean_array_push(x_108, x_128);
x_130 = l_myMacro____x40_Init_Notation___hyg_16009____closed__4;
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = lean_array_push(x_109, x_131);
x_133 = l_myMacro____x40_Init_Notation___hyg_16009____closed__12;
x_134 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_134, 0, x_104);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_array_push(x_108, x_134);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_120);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_array_push(x_132, x_136);
x_138 = lean_array_push(x_137, x_65);
x_139 = l_Lean_Parser_Term_let__fun___elambda__1___closed__2;
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
x_3 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__2;
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
static lean_object* _init_l_Lean_Elab_Term_expandHave___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Array_appendCore___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandHave___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l_Lean_Elab_Term_expandHave___lambda__1___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandHave___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_expandHave___lambda__1___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandHave___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_10, x_11);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_19537____closed__2;
lean_inc(x_16);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Array_empty___closed__1;
x_20 = lean_array_push(x_19, x_18);
x_21 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__5;
lean_inc(x_16);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_array_push(x_19, x_22);
x_24 = l_myMacro____x40_Init_Notation___hyg_22292____closed__3;
lean_inc(x_16);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_array_push(x_19, x_25);
x_27 = lean_array_push(x_26, x_2);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_array_push(x_23, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_myMacro____x40_Init_Notation___hyg_16009____closed__12;
lean_inc(x_16);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_array_push(x_19, x_32);
x_34 = l_Lean_nullKind___closed__2;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_16);
x_36 = l_Lean_Elab_Term_expandHave___lambda__1___closed__3;
x_37 = lean_array_push(x_36, x_6);
x_38 = lean_array_push(x_37, x_30);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_7);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_array_push(x_20, x_39);
x_41 = lean_array_push(x_40, x_35);
x_42 = lean_array_push(x_41, x_13);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_14, 0, x_43);
return x_14;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_44 = lean_ctor_get(x_5, 0);
lean_inc(x_44);
lean_dec(x_5);
x_45 = l_myMacro____x40_Init_Notation___hyg_15440____closed__9;
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_16);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Syntax_mkApp___closed__1;
x_48 = lean_array_push(x_47, x_44);
x_49 = lean_array_push(x_48, x_46);
x_50 = l_Array_appendCore___rarg(x_19, x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_34);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_array_push(x_19, x_51);
x_53 = lean_array_push(x_52, x_6);
x_54 = lean_array_push(x_53, x_30);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_7);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_array_push(x_20, x_55);
x_57 = lean_array_push(x_56, x_35);
x_58 = lean_array_push(x_57, x_13);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_8);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_14, 0, x_59);
return x_14;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_60 = lean_ctor_get(x_14, 0);
x_61 = lean_ctor_get(x_14, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_14);
x_62 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_19537____closed__2;
lean_inc(x_60);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Array_empty___closed__1;
x_65 = lean_array_push(x_64, x_63);
x_66 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__5;
lean_inc(x_60);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_array_push(x_64, x_67);
x_69 = l_myMacro____x40_Init_Notation___hyg_22292____closed__3;
lean_inc(x_60);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_60);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_array_push(x_64, x_70);
x_72 = lean_array_push(x_71, x_2);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_3);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_array_push(x_68, x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_4);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_myMacro____x40_Init_Notation___hyg_16009____closed__12;
lean_inc(x_60);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_60);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_array_push(x_64, x_77);
x_79 = l_Lean_nullKind___closed__2;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_60);
x_81 = l_Lean_Elab_Term_expandHave___lambda__1___closed__3;
x_82 = lean_array_push(x_81, x_6);
x_83 = lean_array_push(x_82, x_75);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_7);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_array_push(x_65, x_84);
x_86 = lean_array_push(x_85, x_80);
x_87 = lean_array_push(x_86, x_13);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_8);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_61);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_90 = lean_ctor_get(x_5, 0);
lean_inc(x_90);
lean_dec(x_5);
x_91 = l_myMacro____x40_Init_Notation___hyg_15440____closed__9;
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_60);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_Syntax_mkApp___closed__1;
x_94 = lean_array_push(x_93, x_90);
x_95 = lean_array_push(x_94, x_92);
x_96 = l_Array_appendCore___rarg(x_64, x_95);
lean_dec(x_95);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_79);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_array_push(x_64, x_97);
x_99 = lean_array_push(x_98, x_6);
x_100 = lean_array_push(x_99, x_75);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_7);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_array_push(x_65, x_101);
x_103 = lean_array_push(x_102, x_80);
x_104 = lean_array_push(x_103, x_13);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_8);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_61);
return x_106;
}
}
}
}
lean_object* l_Lean_Elab_Term_expandHave___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_55 = l_Lean_Elab_Term_expandShow___closed__2;
x_56 = l_Lean_mkIdentFrom(x_5, x_55);
x_57 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_8, x_9);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_12 = x_56;
x_13 = x_58;
x_14 = x_59;
goto block_54;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_56);
x_60 = lean_ctor_get(x_6, 0);
lean_inc(x_60);
lean_dec(x_6);
x_61 = lean_ctor_get(x_57, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_12 = x_60;
x_13 = x_61;
x_14 = x_62;
goto block_54;
}
block_54:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_15 = l_Lean_Parser_Term_let__fun___elambda__1___closed__1;
lean_inc(x_2);
x_16 = lean_name_mk_string(x_2, x_15);
lean_inc(x_13);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Array_empty___closed__1;
x_19 = lean_array_push(x_18, x_17);
x_20 = l_myMacro____x40_Init_Notation___hyg_16009____closed__3;
lean_inc(x_2);
x_21 = lean_name_mk_string(x_2, x_20);
x_22 = l_myMacro____x40_Init_Notation___hyg_16009____closed__5;
lean_inc(x_2);
x_23 = lean_name_mk_string(x_2, x_22);
x_24 = lean_array_push(x_18, x_12);
x_25 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_26 = lean_array_push(x_24, x_25);
x_27 = l_Lean_expandExplicitBindersAux_loop___closed__3;
x_28 = lean_name_mk_string(x_2, x_27);
x_29 = l_myMacro____x40_Init_Notation___hyg_15440____closed__9;
lean_inc(x_13);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_array_push(x_18, x_30);
x_32 = lean_array_push(x_31, x_3);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_array_push(x_18, x_33);
x_35 = l_Lean_nullKind___closed__2;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_array_push(x_26, x_36);
x_38 = l_myMacro____x40_Init_Notation___hyg_16009____closed__11;
lean_inc(x_13);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_13);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_array_push(x_37, x_39);
x_41 = lean_array_push(x_40, x_4);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_23);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_array_push(x_18, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_21);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_push(x_19, x_44);
x_46 = l_myMacro____x40_Init_Notation___hyg_16009____closed__12;
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_13);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_array_push(x_18, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_35);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_array_push(x_45, x_49);
x_51 = lean_array_push(x_50, x_11);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_16);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_14);
return x_53;
}
}
}
lean_object* l_Lean_Elab_Term_expandHave___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__3;
lean_inc(x_2);
x_17 = lean_name_mk_string(x_2, x_16);
lean_inc(x_15);
x_18 = l_Lean_Syntax_isOfKind(x_15, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_19733____closed__2;
lean_inc(x_2);
x_20 = lean_name_mk_string(x_2, x_19);
lean_inc(x_15);
x_21 = l_Lean_Syntax_isOfKind(x_15, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_myMacro____x40_Init_Notation___hyg_22292____closed__1;
x_23 = lean_name_mk_string(x_2, x_22);
lean_inc(x_15);
x_24 = l_Lean_Syntax_isOfKind(x_15, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_25 = lean_box(1);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_11);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = l_Lean_Syntax_getArg(x_15, x_12);
lean_dec(x_15);
x_28 = l_Lean_Parser_Tactic_intro___closed__1;
x_29 = lean_name_mk_string(x_3, x_28);
x_30 = l_Lean_Parser_Tactic_case___closed__7;
x_31 = lean_name_mk_string(x_29, x_30);
lean_inc(x_27);
x_32 = l_Lean_Syntax_isOfKind(x_27, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_33 = lean_box(1);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_11);
return x_34;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Syntax_getArg(x_4, x_14);
x_36 = l_Lean_Syntax_isNone(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_nullKind___closed__2;
lean_inc(x_35);
x_38 = l_Lean_Syntax_isOfKind(x_35, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_35);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_39 = lean_box(1);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_11);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = l_Lean_Syntax_getArgs(x_35);
lean_dec(x_35);
x_42 = lean_array_get_size(x_41);
lean_dec(x_41);
x_43 = lean_nat_dec_eq(x_42, x_12);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_44 = lean_box(1);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_11);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_box(0);
x_47 = l_Lean_Elab_Term_expandHave___lambda__1(x_4, x_27, x_23, x_17, x_9, x_13, x_5, x_6, x_46, x_10, x_11);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_35);
x_48 = lean_box(0);
x_49 = l_Lean_Elab_Term_expandHave___lambda__1(x_4, x_27, x_23, x_17, x_9, x_13, x_5, x_6, x_48, x_10, x_11);
return x_49;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_50 = l_Lean_Syntax_getArg(x_15, x_12);
lean_dec(x_15);
x_51 = l_Lean_Syntax_getArg(x_4, x_14);
x_52 = l_Lean_Syntax_isNone(x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = l_Lean_nullKind___closed__2;
lean_inc(x_51);
x_54 = l_Lean_Syntax_isOfKind(x_51, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_2);
x_55 = lean_box(1);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_11);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = l_Lean_Syntax_getArgs(x_51);
lean_dec(x_51);
x_58 = lean_array_get_size(x_57);
lean_dec(x_57);
x_59 = lean_nat_dec_eq(x_58, x_12);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_50);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_2);
x_60 = lean_box(1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_11);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_box(0);
x_63 = l_Lean_Elab_Term_expandHave___lambda__2(x_4, x_2, x_13, x_50, x_7, x_9, x_62, x_10, x_11);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_51);
x_64 = lean_box(0);
x_65 = l_Lean_Elab_Term_expandHave___lambda__2(x_4, x_2, x_13, x_50, x_7, x_9, x_64, x_10, x_11);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_66 = l_Lean_Syntax_getArg(x_15, x_12);
lean_dec(x_15);
x_67 = l_Lean_Syntax_getArg(x_4, x_14);
x_68 = l_Lean_Syntax_isNone(x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = l_Lean_nullKind___closed__2;
lean_inc(x_67);
x_70 = l_Lean_Syntax_isOfKind(x_67, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_2);
x_71 = lean_box(1);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_11);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = l_Lean_Syntax_getArgs(x_67);
lean_dec(x_67);
x_74 = lean_array_get_size(x_73);
lean_dec(x_73);
x_75 = lean_nat_dec_eq(x_74, x_12);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_66);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_2);
x_76 = lean_box(1);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_11);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_box(0);
x_79 = l_Lean_Elab_Term_expandHave___lambda__2(x_4, x_2, x_13, x_66, x_7, x_9, x_78, x_10, x_11);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_67);
x_80 = lean_box(0);
x_81 = l_Lean_Elab_Term_expandHave___lambda__2(x_4, x_2, x_13, x_66, x_7, x_9, x_80, x_10, x_11);
return x_81;
}
}
}
}
lean_object* l_Lean_Elab_Term_expandHave(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_19537____closed__3;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_19733____closed__1;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_1);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_9, x_14);
x_16 = l_Lean_Syntax_isNone(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_nullKind___closed__2;
lean_inc(x_15);
x_18 = l_Lean_Syntax_isOfKind(x_15, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = l_Lean_Syntax_getArgs(x_15);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_1);
x_25 = lean_box(1);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = l_Lean_Syntax_getArg(x_15, x_14);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
x_30 = l_Lean_Parser_Syntax_addPrec___closed__4;
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Term_expandHave___lambda__3(x_9, x_29, x_30, x_1, x_10, x_4, x_1, x_31, x_28, x_2, x_3);
lean_dec(x_1);
lean_dec(x_9);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_15);
x_33 = lean_box(0);
x_34 = l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
x_35 = l_Lean_Parser_Syntax_addPrec___closed__4;
x_36 = lean_box(0);
x_37 = l_Lean_Elab_Term_expandHave___lambda__3(x_9, x_34, x_35, x_1, x_10, x_4, x_1, x_36, x_33, x_2, x_3);
lean_dec(x_1);
lean_dec(x_9);
return x_37;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_expandHave___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_expandHave___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_expandHave___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_expandHave___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_expandHave___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_expandHave___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
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
x_3 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_19537____closed__3;
x_4 = l___regBuiltin_Lean_Elab_Term_expandHave___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandSuffices___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_9, x_10);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_19537____closed__2;
lean_inc(x_2);
x_17 = lean_name_mk_string(x_2, x_16);
lean_inc(x_15);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Array_empty___closed__1;
x_20 = lean_array_push(x_19, x_18);
x_21 = l_Lean_Parser_Tactic_tacticHave_____closed__5;
x_22 = lean_name_mk_string(x_2, x_21);
x_23 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__5;
lean_inc(x_15);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_array_push(x_19, x_24);
x_26 = lean_array_push(x_25, x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_myMacro____x40_Init_Notation___hyg_16009____closed__12;
lean_inc(x_15);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_array_push(x_19, x_29);
x_31 = l_Lean_nullKind___closed__2;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_myMacro____x40_Init_Notation___hyg_22292____closed__3;
lean_inc(x_15);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_array_push(x_19, x_34);
x_36 = lean_array_push(x_35, x_4);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_36);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_15);
x_38 = l_Lean_Elab_Term_expandHave___lambda__1___closed__3;
x_39 = lean_array_push(x_38, x_7);
x_40 = lean_array_push(x_39, x_27);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_22);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_array_push(x_20, x_41);
x_43 = lean_array_push(x_42, x_32);
x_44 = lean_array_push(x_43, x_37);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_17);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_13, 0, x_45);
return x_13;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_46 = lean_ctor_get(x_6, 0);
lean_inc(x_46);
lean_dec(x_6);
x_47 = l_myMacro____x40_Init_Notation___hyg_15440____closed__9;
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_15);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Syntax_mkApp___closed__1;
x_50 = lean_array_push(x_49, x_46);
x_51 = lean_array_push(x_50, x_48);
x_52 = l_Array_appendCore___rarg(x_19, x_51);
lean_dec(x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_31);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_array_push(x_19, x_53);
x_55 = lean_array_push(x_54, x_7);
x_56 = lean_array_push(x_55, x_27);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_22);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_array_push(x_20, x_57);
x_59 = lean_array_push(x_58, x_32);
x_60 = lean_array_push(x_59, x_37);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_17);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_13, 0, x_61);
return x_13;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_62 = lean_ctor_get(x_13, 0);
x_63 = lean_ctor_get(x_13, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_13);
x_64 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_19537____closed__2;
lean_inc(x_2);
x_65 = lean_name_mk_string(x_2, x_64);
lean_inc(x_62);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Array_empty___closed__1;
x_68 = lean_array_push(x_67, x_66);
x_69 = l_Lean_Parser_Tactic_tacticHave_____closed__5;
x_70 = lean_name_mk_string(x_2, x_69);
x_71 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__5;
lean_inc(x_62);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_array_push(x_67, x_72);
x_74 = lean_array_push(x_73, x_12);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_3);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_myMacro____x40_Init_Notation___hyg_16009____closed__12;
lean_inc(x_62);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_62);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_array_push(x_67, x_77);
x_79 = l_Lean_nullKind___closed__2;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_myMacro____x40_Init_Notation___hyg_22292____closed__3;
lean_inc(x_62);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_62);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_array_push(x_67, x_82);
x_84 = lean_array_push(x_83, x_4);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_5);
lean_ctor_set(x_85, 1, x_84);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_62);
x_86 = l_Lean_Elab_Term_expandHave___lambda__1___closed__3;
x_87 = lean_array_push(x_86, x_7);
x_88 = lean_array_push(x_87, x_75);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_70);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_array_push(x_68, x_89);
x_91 = lean_array_push(x_90, x_80);
x_92 = lean_array_push(x_91, x_85);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_65);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_63);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_95 = lean_ctor_get(x_6, 0);
lean_inc(x_95);
lean_dec(x_6);
x_96 = l_myMacro____x40_Init_Notation___hyg_15440____closed__9;
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_62);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Syntax_mkApp___closed__1;
x_99 = lean_array_push(x_98, x_95);
x_100 = lean_array_push(x_99, x_97);
x_101 = l_Array_appendCore___rarg(x_67, x_100);
lean_dec(x_100);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_79);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_array_push(x_67, x_102);
x_104 = lean_array_push(x_103, x_7);
x_105 = lean_array_push(x_104, x_75);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_70);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_array_push(x_68, x_106);
x_108 = lean_array_push(x_107, x_80);
x_109 = lean_array_push(x_108, x_85);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_65);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_63);
return x_111;
}
}
}
}
lean_object* l_Lean_Elab_Term_expandSuffices___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_8, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_19537____closed__2;
lean_inc(x_2);
x_16 = lean_name_mk_string(x_2, x_15);
lean_inc(x_14);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Array_empty___closed__1;
x_19 = lean_array_push(x_18, x_17);
x_20 = l_Lean_Parser_Tactic_tacticHave_____closed__5;
x_21 = lean_name_mk_string(x_2, x_20);
x_22 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__5;
lean_inc(x_14);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_array_push(x_18, x_23);
x_25 = lean_array_push(x_24, x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_myMacro____x40_Init_Notation___hyg_16009____closed__12;
lean_inc(x_14);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_array_push(x_18, x_28);
x_30 = l_Lean_nullKind___closed__2;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_14);
x_32 = l_Lean_Elab_Term_expandHave___lambda__1___closed__3;
x_33 = lean_array_push(x_32, x_5);
x_34 = lean_array_push(x_33, x_26);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_array_push(x_19, x_35);
x_37 = lean_array_push(x_36, x_31);
x_38 = lean_array_push(x_37, x_6);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_16);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_12, 0, x_39);
return x_12;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_40 = lean_ctor_get(x_4, 0);
lean_inc(x_40);
lean_dec(x_4);
x_41 = l_myMacro____x40_Init_Notation___hyg_15440____closed__9;
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_14);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Syntax_mkApp___closed__1;
x_44 = lean_array_push(x_43, x_40);
x_45 = lean_array_push(x_44, x_42);
x_46 = l_Array_appendCore___rarg(x_18, x_45);
lean_dec(x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_30);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_array_push(x_18, x_47);
x_49 = lean_array_push(x_48, x_5);
x_50 = lean_array_push(x_49, x_26);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_21);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_array_push(x_19, x_51);
x_53 = lean_array_push(x_52, x_31);
x_54 = lean_array_push(x_53, x_6);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_16);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_12, 0, x_55);
return x_12;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_56 = lean_ctor_get(x_12, 0);
x_57 = lean_ctor_get(x_12, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_12);
x_58 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_19537____closed__2;
lean_inc(x_2);
x_59 = lean_name_mk_string(x_2, x_58);
lean_inc(x_56);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_58);
x_61 = l_Array_empty___closed__1;
x_62 = lean_array_push(x_61, x_60);
x_63 = l_Lean_Parser_Tactic_tacticHave_____closed__5;
x_64 = lean_name_mk_string(x_2, x_63);
x_65 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__5;
lean_inc(x_56);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_56);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_array_push(x_61, x_66);
x_68 = lean_array_push(x_67, x_11);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_3);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_myMacro____x40_Init_Notation___hyg_16009____closed__12;
lean_inc(x_56);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_56);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_array_push(x_61, x_71);
x_73 = l_Lean_nullKind___closed__2;
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_56);
x_75 = l_Lean_Elab_Term_expandHave___lambda__1___closed__3;
x_76 = lean_array_push(x_75, x_5);
x_77 = lean_array_push(x_76, x_69);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_64);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_array_push(x_62, x_78);
x_80 = lean_array_push(x_79, x_74);
x_81 = lean_array_push(x_80, x_6);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_59);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_57);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_84 = lean_ctor_get(x_4, 0);
lean_inc(x_84);
lean_dec(x_4);
x_85 = l_myMacro____x40_Init_Notation___hyg_15440____closed__9;
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_56);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_Syntax_mkApp___closed__1;
x_88 = lean_array_push(x_87, x_84);
x_89 = lean_array_push(x_88, x_86);
x_90 = l_Array_appendCore___rarg(x_61, x_89);
lean_dec(x_89);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_73);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_array_push(x_61, x_91);
x_93 = lean_array_push(x_92, x_5);
x_94 = lean_array_push(x_93, x_69);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_64);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_array_push(x_62, x_95);
x_97 = lean_array_push(x_96, x_74);
x_98 = lean_array_push(x_97, x_6);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_59);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_57);
return x_100;
}
}
}
}
lean_object* l_Lean_Elab_Term_expandSuffices___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20302____closed__3;
lean_inc(x_2);
x_14 = lean_name_mk_string(x_2, x_13);
lean_inc(x_12);
x_15 = l_Lean_Syntax_isOfKind(x_12, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_myMacro____x40_Init_Notation___hyg_22292____closed__1;
lean_inc(x_2);
x_17 = lean_name_mk_string(x_2, x_16);
lean_inc(x_12);
x_18 = l_Lean_Syntax_isOfKind(x_12, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_box(1);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = l_Lean_Syntax_getArg(x_12, x_9);
lean_dec(x_12);
x_22 = l_Lean_Parser_Tactic_intro___closed__1;
x_23 = lean_name_mk_string(x_3, x_22);
x_24 = l_Lean_Parser_Tactic_case___closed__7;
x_25 = lean_name_mk_string(x_23, x_24);
lean_inc(x_21);
x_26 = l_Lean_Syntax_isOfKind(x_21, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_2);
x_27 = lean_box(1);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Syntax_getArg(x_4, x_11);
x_30 = l_Lean_Syntax_isNone(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_nullKind___closed__2;
lean_inc(x_29);
x_32 = l_Lean_Syntax_isOfKind(x_29, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_29);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_2);
x_33 = lean_box(1);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_8);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = l_Lean_Syntax_getArgs(x_29);
lean_dec(x_29);
x_36 = lean_array_get_size(x_35);
lean_dec(x_35);
x_37 = lean_nat_dec_eq(x_36, x_9);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_2);
x_38 = lean_box(1);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_8);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_box(0);
x_41 = l_Lean_Elab_Term_expandSuffices___lambda__1(x_4, x_2, x_14, x_21, x_17, x_6, x_10, x_40, x_7, x_8);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_29);
x_42 = lean_box(0);
x_43 = l_Lean_Elab_Term_expandSuffices___lambda__1(x_4, x_2, x_14, x_21, x_17, x_6, x_10, x_42, x_7, x_8);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_3);
x_44 = l_Lean_Syntax_getArg(x_12, x_9);
lean_dec(x_12);
x_45 = l_Lean_Syntax_getArg(x_4, x_11);
x_46 = l_Lean_Syntax_isNone(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = l_Lean_nullKind___closed__2;
lean_inc(x_45);
x_48 = l_Lean_Syntax_isOfKind(x_45, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_2);
x_49 = lean_box(1);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_8);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = l_Lean_Syntax_getArgs(x_45);
lean_dec(x_45);
x_52 = lean_array_get_size(x_51);
lean_dec(x_51);
x_53 = lean_nat_dec_eq(x_52, x_9);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_44);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_2);
x_54 = lean_box(1);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_8);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_box(0);
x_57 = l_Lean_Elab_Term_expandSuffices___lambda__2(x_4, x_2, x_14, x_6, x_10, x_44, x_56, x_7, x_8);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_45);
x_58 = lean_box(0);
x_59 = l_Lean_Elab_Term_expandSuffices___lambda__2(x_4, x_2, x_14, x_6, x_10, x_44, x_58, x_7, x_8);
return x_59;
}
}
}
}
lean_object* l_Lean_Elab_Term_expandSuffices(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_19931____closed__2;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Parser_Term_sufficesDecl___elambda__1___closed__1;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_1);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_9, x_14);
x_16 = l_Lean_Syntax_isNone(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_nullKind___closed__2;
lean_inc(x_15);
x_18 = l_Lean_Syntax_isOfKind(x_15, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = l_Lean_Syntax_getArgs(x_15);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_1);
x_25 = lean_box(1);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = l_Lean_Syntax_getArg(x_15, x_14);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
x_30 = l_Lean_Parser_Syntax_addPrec___closed__4;
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Term_expandSuffices___lambda__3(x_9, x_29, x_30, x_1, x_31, x_28, x_2, x_3);
lean_dec(x_1);
lean_dec(x_9);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_15);
x_33 = lean_box(0);
x_34 = l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
x_35 = l_Lean_Parser_Syntax_addPrec___closed__4;
x_36 = lean_box(0);
x_37 = l_Lean_Elab_Term_expandSuffices___lambda__3(x_9, x_34, x_35, x_1, x_36, x_33, x_2, x_3);
lean_dec(x_1);
lean_dec(x_9);
return x_37;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_expandSuffices___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_expandSuffices___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_expandSuffices___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_expandSuffices___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_expandSuffices___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_expandSuffices___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
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
x_3 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_19931____closed__2;
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
x_1 = lean_mk_string("invalid `leading_parser` macro, it must be used in definitions");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid `leading_parser` macro, unexpected declaration name");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Parser.leadingNode");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__5;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("leadingNode");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__4;
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("OrElse.orElse");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__12;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__12;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__13;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("OrElse");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("orElse");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__16;
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__18;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__19;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Parser.mkAntiquot");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__21;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__21;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__22;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkAntiquot");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__4;
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__24;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__26;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprOption___rarg___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_instReprOption___rarg___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__28;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_instReprOption___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__31() {
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
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__31;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__5;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__33;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__36() {
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
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__36;
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
x_13 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__2;
x_14 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__6(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_19 = lean_ctor_get(x_17, 3);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Init_Meta_0__Lean_quoteName(x_16);
x_22 = lean_box(2);
x_23 = l_Lean_Syntax_mkStrLit(x_20, x_22);
lean_dec(x_20);
x_24 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_7, x_8, x_15);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__9;
x_34 = l_Lean_addMacroScope(x_31, x_33, x_28);
x_35 = lean_box(0);
x_36 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__7;
x_37 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__11;
x_38 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_37);
x_39 = l_Array_empty___closed__1;
x_40 = lean_array_push(x_39, x_38);
x_41 = lean_array_push(x_39, x_21);
lean_inc(x_41);
x_42 = lean_array_push(x_41, x_1);
x_43 = lean_array_push(x_42, x_2);
x_44 = l_Lean_nullKind___closed__2;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_array_push(x_40, x_45);
x_47 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_List_beq___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___spec__1(x_19, x_35);
lean_dec(x_19);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_41);
x_50 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg(x_7, x_8, x_32);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_52);
lean_dec(x_3);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_55);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__18;
lean_inc(x_54);
lean_inc(x_58);
x_60 = l_Lean_addMacroScope(x_58, x_59, x_54);
x_61 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14;
x_62 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20;
lean_inc(x_51);
x_63 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_63, 0, x_51);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_60);
lean_ctor_set(x_63, 3, x_62);
x_64 = lean_array_push(x_39, x_63);
x_65 = l_prec_x28___x29___closed__3;
lean_inc(x_51);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_51);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_array_push(x_39, x_66);
x_68 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25;
lean_inc(x_54);
lean_inc(x_58);
x_69 = l_Lean_addMacroScope(x_58, x_68, x_54);
x_70 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23;
x_71 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27;
lean_inc(x_51);
x_72 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_72, 0, x_51);
lean_ctor_set(x_72, 1, x_70);
lean_ctor_set(x_72, 2, x_69);
lean_ctor_set(x_72, 3, x_71);
x_73 = lean_array_push(x_39, x_72);
x_74 = lean_array_push(x_39, x_23);
x_75 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__30;
x_76 = l_Lean_addMacroScope(x_58, x_75, x_54);
x_77 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29;
x_78 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__32;
lean_inc(x_51);
x_79 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_79, 0, x_51);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_79, 2, x_76);
lean_ctor_set(x_79, 3, x_78);
x_80 = lean_array_push(x_74, x_79);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_44);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_array_push(x_73, x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_47);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_array_push(x_39, x_83);
x_85 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_86 = lean_array_push(x_84, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_44);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_array_push(x_67, x_87);
x_89 = l_prec_x28___x29___closed__7;
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_51);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_array_push(x_88, x_90);
x_92 = l_myMacro____x40_Init_Notation___hyg_13918____closed__8;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_array_push(x_39, x_93);
x_95 = lean_array_push(x_94, x_48);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_44);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_array_push(x_64, x_96);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_47);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_56, 0, x_98);
return x_56;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_99 = lean_ctor_get(x_56, 0);
x_100 = lean_ctor_get(x_56, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_56);
x_101 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__18;
lean_inc(x_54);
lean_inc(x_99);
x_102 = l_Lean_addMacroScope(x_99, x_101, x_54);
x_103 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14;
x_104 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20;
lean_inc(x_51);
x_105 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_105, 0, x_51);
lean_ctor_set(x_105, 1, x_103);
lean_ctor_set(x_105, 2, x_102);
lean_ctor_set(x_105, 3, x_104);
x_106 = lean_array_push(x_39, x_105);
x_107 = l_prec_x28___x29___closed__3;
lean_inc(x_51);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_51);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_array_push(x_39, x_108);
x_110 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25;
lean_inc(x_54);
lean_inc(x_99);
x_111 = l_Lean_addMacroScope(x_99, x_110, x_54);
x_112 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23;
x_113 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27;
lean_inc(x_51);
x_114 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_114, 0, x_51);
lean_ctor_set(x_114, 1, x_112);
lean_ctor_set(x_114, 2, x_111);
lean_ctor_set(x_114, 3, x_113);
x_115 = lean_array_push(x_39, x_114);
x_116 = lean_array_push(x_39, x_23);
x_117 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__30;
x_118 = l_Lean_addMacroScope(x_99, x_117, x_54);
x_119 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__29;
x_120 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__32;
lean_inc(x_51);
x_121 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_121, 0, x_51);
lean_ctor_set(x_121, 1, x_119);
lean_ctor_set(x_121, 2, x_118);
lean_ctor_set(x_121, 3, x_120);
x_122 = lean_array_push(x_116, x_121);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_44);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_array_push(x_115, x_123);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_47);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_array_push(x_39, x_125);
x_127 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_128 = lean_array_push(x_126, x_127);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_44);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_array_push(x_109, x_129);
x_131 = l_prec_x28___x29___closed__7;
x_132 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_132, 0, x_51);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_array_push(x_130, x_132);
x_134 = l_myMacro____x40_Init_Notation___hyg_13918____closed__8;
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = lean_array_push(x_39, x_135);
x_137 = lean_array_push(x_136, x_48);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_44);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_array_push(x_106, x_138);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_47);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_100);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_142 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg(x_7, x_8, x_32);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_144);
lean_dec(x_3);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_147);
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_150 = lean_ctor_get(x_148, 0);
x_151 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__18;
lean_inc(x_146);
lean_inc(x_150);
x_152 = l_Lean_addMacroScope(x_150, x_151, x_146);
x_153 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14;
x_154 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20;
lean_inc(x_143);
x_155 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_155, 0, x_143);
lean_ctor_set(x_155, 1, x_153);
lean_ctor_set(x_155, 2, x_152);
lean_ctor_set(x_155, 3, x_154);
x_156 = lean_array_push(x_39, x_155);
x_157 = l_prec_x28___x29___closed__3;
lean_inc(x_143);
x_158 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_158, 0, x_143);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_array_push(x_39, x_158);
x_160 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25;
lean_inc(x_146);
lean_inc(x_150);
x_161 = l_Lean_addMacroScope(x_150, x_160, x_146);
x_162 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23;
x_163 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27;
lean_inc(x_143);
x_164 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_164, 0, x_143);
lean_ctor_set(x_164, 1, x_162);
lean_ctor_set(x_164, 2, x_161);
lean_ctor_set(x_164, 3, x_163);
x_165 = lean_array_push(x_39, x_164);
x_166 = lean_array_push(x_39, x_23);
x_167 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__35;
x_168 = l_Lean_addMacroScope(x_150, x_167, x_146);
x_169 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__34;
x_170 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__37;
lean_inc(x_143);
x_171 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_171, 0, x_143);
lean_ctor_set(x_171, 1, x_169);
lean_ctor_set(x_171, 2, x_168);
lean_ctor_set(x_171, 3, x_170);
x_172 = lean_array_push(x_39, x_171);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_44);
lean_ctor_set(x_173, 1, x_41);
x_174 = lean_array_push(x_172, x_173);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_47);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_array_push(x_39, x_175);
x_177 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_178 = lean_array_push(x_176, x_177);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_44);
lean_ctor_set(x_179, 1, x_178);
lean_inc(x_159);
x_180 = lean_array_push(x_159, x_179);
x_181 = l_prec_x28___x29___closed__7;
x_182 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_182, 0, x_143);
lean_ctor_set(x_182, 1, x_181);
lean_inc(x_182);
x_183 = lean_array_push(x_180, x_182);
x_184 = l_myMacro____x40_Init_Notation___hyg_13918____closed__8;
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
x_186 = lean_array_push(x_166, x_185);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_44);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_array_push(x_165, x_187);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_47);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_array_push(x_39, x_189);
x_191 = lean_array_push(x_190, x_177);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_44);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_array_push(x_159, x_192);
x_194 = lean_array_push(x_193, x_182);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_184);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_array_push(x_39, x_195);
x_197 = lean_array_push(x_196, x_48);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_44);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_array_push(x_156, x_198);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_47);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set(x_148, 0, x_200);
return x_148;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_201 = lean_ctor_get(x_148, 0);
x_202 = lean_ctor_get(x_148, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_148);
x_203 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__18;
lean_inc(x_146);
lean_inc(x_201);
x_204 = l_Lean_addMacroScope(x_201, x_203, x_146);
x_205 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__14;
x_206 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__20;
lean_inc(x_143);
x_207 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_207, 0, x_143);
lean_ctor_set(x_207, 1, x_205);
lean_ctor_set(x_207, 2, x_204);
lean_ctor_set(x_207, 3, x_206);
x_208 = lean_array_push(x_39, x_207);
x_209 = l_prec_x28___x29___closed__3;
lean_inc(x_143);
x_210 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_210, 0, x_143);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_array_push(x_39, x_210);
x_212 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__25;
lean_inc(x_146);
lean_inc(x_201);
x_213 = l_Lean_addMacroScope(x_201, x_212, x_146);
x_214 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__23;
x_215 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__27;
lean_inc(x_143);
x_216 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_216, 0, x_143);
lean_ctor_set(x_216, 1, x_214);
lean_ctor_set(x_216, 2, x_213);
lean_ctor_set(x_216, 3, x_215);
x_217 = lean_array_push(x_39, x_216);
x_218 = lean_array_push(x_39, x_23);
x_219 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__35;
x_220 = l_Lean_addMacroScope(x_201, x_219, x_146);
x_221 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__34;
x_222 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__37;
lean_inc(x_143);
x_223 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_223, 0, x_143);
lean_ctor_set(x_223, 1, x_221);
lean_ctor_set(x_223, 2, x_220);
lean_ctor_set(x_223, 3, x_222);
x_224 = lean_array_push(x_39, x_223);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_44);
lean_ctor_set(x_225, 1, x_41);
x_226 = lean_array_push(x_224, x_225);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_47);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_array_push(x_39, x_227);
x_229 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_230 = lean_array_push(x_228, x_229);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_44);
lean_ctor_set(x_231, 1, x_230);
lean_inc(x_211);
x_232 = lean_array_push(x_211, x_231);
x_233 = l_prec_x28___x29___closed__7;
x_234 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_234, 0, x_143);
lean_ctor_set(x_234, 1, x_233);
lean_inc(x_234);
x_235 = lean_array_push(x_232, x_234);
x_236 = l_myMacro____x40_Init_Notation___hyg_13918____closed__8;
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_235);
x_238 = lean_array_push(x_218, x_237);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_44);
lean_ctor_set(x_239, 1, x_238);
x_240 = lean_array_push(x_217, x_239);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_47);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_array_push(x_39, x_241);
x_243 = lean_array_push(x_242, x_229);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_44);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_array_push(x_211, x_244);
x_246 = lean_array_push(x_245, x_234);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_236);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_array_push(x_39, x_247);
x_249 = lean_array_push(x_248, x_48);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_44);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_array_push(x_208, x_250);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_47);
lean_ctor_set(x_252, 1, x_251);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_202);
return x_253;
}
}
}
else
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_254 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabParserMacroAux___closed__4;
x_255 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__6(x_254, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_255;
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
static lean_object* _init_l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_maxPrec;
x_2 = l_Nat_repr(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_numLitKind;
x_2 = l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1___closed__1;
x_3 = lean_box(2);
x_4 = l_Lean_Syntax_mkLit(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Parser_Term_leading__parser___elambda__1___closed__2;
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg(x_8);
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
x_37 = l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1___closed__2;
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
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg(x_8);
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
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg(x_8);
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
static lean_object* _init_l_Lean_Elab_Term_elabLeadingParserMacro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1___boxed), 8, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_elabLeadingParserMacro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_elabLeadingParserMacro___closed__1;
x_11 = l_Lean_Elab_Term_adaptExpander(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLeadingParserMacro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLeadingParserMacro), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabLeadingParserMacro(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_leading__parser___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabLeadingParserMacro___closed__1;
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
x_1 = lean_mk_string("invalid `trailing_parser` macro, it must be used in definitions");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Parser.trailingNode");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trailingNode");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__4;
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Term_getDeclName_x3f(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__2;
x_15 = l_Lean_throwError___at_Lean_Elab_Term_quoteAutoTactic___spec__6(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = l___private_Init_Meta_0__Lean_quoteName(x_17);
x_19 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg(x_8, x_9, x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_4);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__7;
x_29 = l_Lean_addMacroScope(x_27, x_28, x_23);
x_30 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__5;
x_31 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__9;
x_32 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_29);
lean_ctor_set(x_32, 3, x_31);
x_33 = l_Array_empty___closed__1;
x_34 = lean_array_push(x_33, x_32);
x_35 = lean_array_push(x_33, x_18);
x_36 = lean_array_push(x_35, x_1);
x_37 = lean_array_push(x_36, x_2);
x_38 = lean_array_push(x_37, x_3);
x_39 = l_Lean_nullKind___closed__2;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_array_push(x_34, x_40);
x_42 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_25, 0, x_43);
return x_25;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_44 = lean_ctor_get(x_25, 0);
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_25);
x_46 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__7;
x_47 = l_Lean_addMacroScope(x_44, x_46, x_23);
x_48 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__5;
x_49 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___closed__9;
x_50 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_50, 0, x_20);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set(x_50, 2, x_47);
lean_ctor_set(x_50, 3, x_49);
x_51 = l_Array_empty___closed__1;
x_52 = lean_array_push(x_51, x_50);
x_53 = lean_array_push(x_51, x_18);
x_54 = lean_array_push(x_53, x_1);
x_55 = lean_array_push(x_54, x_2);
x_56 = lean_array_push(x_55, x_3);
x_57 = l_Lean_nullKind___closed__2;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_array_push(x_52, x_58);
x_60 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_45);
return x_62;
}
}
}
}
lean_object* l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabTrailingParserMacro___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_numLitKind;
x_2 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__8___lambda__1___closed__1;
x_3 = lean_box(2);
x_4 = l_Lean_Syntax_mkLit(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabTrailingParserMacro___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1___closed__2;
x_15 = l_Lean_Elab_Term_elabTrailingParserMacro___lambda__1___closed__1;
x_16 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(x_14, x_15, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec(x_4);
x_18 = l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1___closed__2;
x_19 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(x_18, x_17, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_19;
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = l_Lean_Elab_Term_elabTrailingParserMacro___lambda__1___closed__1;
x_22 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(x_20, x_21, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
lean_dec(x_4);
x_25 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabTParserMacroAux(x_23, x_24, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_25;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabTrailingParserMacro___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_isNone(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_nullKind___closed__2;
lean_inc(x_12);
x_15 = l_Lean_Syntax_isOfKind(x_12, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg(x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l_Lean_Syntax_getArgs(x_12);
x_18 = lean_array_get_size(x_17);
lean_dec(x_17);
x_19 = lean_nat_dec_eq(x_18, x_11);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg(x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Syntax_getArg(x_12, x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Term_elabTrailingParserMacro___lambda__1(x_1, x_3, x_24, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_12);
x_26 = lean_box(0);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Term_elabTrailingParserMacro___lambda__1(x_1, x_3, x_27, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_28;
}
}
}
lean_object* l_Lean_Elab_Term_elabTrailingParserMacro___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Parser_Term_trailing__parser___elambda__1___closed__2;
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg(x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_isNone(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_nullKind___closed__2;
lean_inc(x_13);
x_16 = l_Lean_Syntax_isOfKind(x_13, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg(x_8);
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
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_expandBinderModifier___spec__1___rarg(x_8);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = l_Lean_Syntax_getArg(x_13, x_12);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_box(0);
x_26 = l_Lean_Elab_Term_elabTrailingParserMacro___lambda__2(x_1, x_25, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_13);
x_27 = lean_box(0);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Term_elabTrailingParserMacro___lambda__2(x_1, x_28, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_29;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabTrailingParserMacro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTrailingParserMacro___lambda__3___boxed), 8, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_elabTrailingParserMacro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_elabTrailingParserMacro___closed__1;
x_11 = l_Lean_Elab_Term_adaptExpander(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabTrailingParserMacro___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_elabTrailingParserMacro___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_elabTrailingParserMacro___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_elabTrailingParserMacro___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabTrailingParserMacro___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabTrailingParserMacro___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTrailingParserMacro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTrailingParserMacro), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabTrailingParserMacro(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_trailing__parser___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabTrailingParserMacro___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = 0;
x_6 = l_Lean_Syntax_getPos_x3f(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
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
lean_dec(x_11);
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
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_7, x_8, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_Term_elabPanic___closed__4;
x_32 = l_Lean_addMacroScope(x_29, x_31, x_26);
x_33 = l_Lean_Elab_Term_elabPanic___closed__3;
x_34 = l_Lean_Elab_Term_elabPanic___closed__6;
x_35 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_32);
lean_ctor_set(x_35, 3, x_34);
x_36 = l_Array_empty___closed__1;
x_37 = lean_array_push(x_36, x_35);
x_38 = lean_environment_main_module(x_18);
x_39 = l_Lean_Name_toString___closed__1;
x_40 = l_Lean_Name_toStringWithSep(x_39, x_38);
x_41 = lean_box(2);
x_42 = l_Lean_Syntax_mkStrLit(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_push(x_36, x_42);
x_44 = lean_ctor_get(x_13, 0);
lean_inc(x_44);
x_45 = l_Nat_repr(x_44);
x_46 = l_Lean_numLitKind;
x_47 = l_Lean_Syntax_mkLit(x_46, x_45, x_41);
x_48 = lean_array_push(x_43, x_47);
x_49 = lean_ctor_get(x_13, 1);
lean_inc(x_49);
lean_dec(x_13);
x_50 = l_Nat_repr(x_49);
x_51 = l_Lean_Syntax_mkLit(x_46, x_50, x_41);
x_52 = lean_array_push(x_48, x_51);
x_53 = lean_array_push(x_52, x_11);
x_54 = l_Lean_nullKind___closed__2;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_array_push(x_37, x_55);
x_57 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_Elab_Term_elabAnonymousCtor___lambda__2(x_1, x_2, x_58, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_60 = lean_ctor_get(x_19, 1);
lean_inc(x_60);
lean_dec(x_19);
x_61 = lean_ctor_get(x_20, 0);
lean_inc(x_61);
lean_dec(x_20);
x_62 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_7, x_8, x_60);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Elab_Term_elabPanic___closed__10;
x_72 = l_Lean_addMacroScope(x_69, x_71, x_66);
x_73 = l_Lean_Elab_Term_elabPanic___closed__9;
x_74 = l_Lean_Elab_Term_elabPanic___closed__12;
x_75 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_75, 0, x_63);
lean_ctor_set(x_75, 1, x_73);
lean_ctor_set(x_75, 2, x_72);
lean_ctor_set(x_75, 3, x_74);
x_76 = l_Array_empty___closed__1;
x_77 = lean_array_push(x_76, x_75);
x_78 = lean_environment_main_module(x_18);
x_79 = l_Lean_Name_toString___closed__1;
x_80 = l_Lean_Name_toStringWithSep(x_79, x_78);
x_81 = lean_box(2);
x_82 = l_Lean_Syntax_mkStrLit(x_80, x_81);
lean_dec(x_80);
x_83 = lean_array_push(x_76, x_82);
x_84 = l_Lean_Name_toStringWithSep(x_79, x_61);
x_85 = l_Lean_Syntax_mkStrLit(x_84, x_81);
lean_dec(x_84);
x_86 = lean_array_push(x_83, x_85);
x_87 = lean_ctor_get(x_13, 0);
lean_inc(x_87);
x_88 = l_Nat_repr(x_87);
x_89 = l_Lean_numLitKind;
x_90 = l_Lean_Syntax_mkLit(x_89, x_88, x_81);
x_91 = lean_array_push(x_86, x_90);
x_92 = lean_ctor_get(x_13, 1);
lean_inc(x_92);
lean_dec(x_13);
x_93 = l_Nat_repr(x_92);
x_94 = l_Lean_Syntax_mkLit(x_89, x_93, x_81);
x_95 = lean_array_push(x_91, x_94);
x_96 = lean_array_push(x_95, x_11);
x_97 = l_Lean_nullKind___closed__2;
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_array_push(x_77, x_98);
x_100 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_Lean_Elab_Term_elabAnonymousCtor___lambda__2(x_1, x_2, x_101, x_3, x_4, x_5, x_6, x_7, x_8, x_70);
return x_102;
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
x_3 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_1, x_2);
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
x_1 = lean_mk_string("\"assertion violation\"");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandAssert___closed__3() {
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
x_9 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_2, x_3);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_Parser_Term_notFollowedByRedefinedTermToken___elambda__1___closed__43;
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
x_21 = l_termDepIfThenElse___closed__24;
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
x_30 = l_Lean_Elab_Term_expandAssert___closed__2;
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
x_36 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
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
x_44 = l_myMacro____x40_Init_Notation___hyg_13918____closed__8;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_array_push(x_26, x_45);
x_47 = l_Lean_Parser_Term_panic___elambda__1___closed__2;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_array_push(x_23, x_48);
x_50 = l_termIfThenElse___closed__2;
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
x_54 = l_Lean_Parser_Term_notFollowedByRedefinedTermToken___elambda__1___closed__43;
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
x_63 = l_termDepIfThenElse___closed__24;
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
x_72 = l_Lean_Elab_Term_expandAssert___closed__2;
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
x_78 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
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
x_86 = l_myMacro____x40_Init_Notation___hyg_13918____closed__8;
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_array_push(x_68, x_87);
x_89 = l_Lean_Parser_Term_panic___elambda__1___closed__2;
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_array_push(x_65, x_90);
x_92 = l_termIfThenElse___closed__2;
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
x_96 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_2, x_3);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = l_Lean_Parser_Term_notFollowedByRedefinedTermToken___elambda__1___closed__43;
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
x_108 = l_termDepIfThenElse___closed__24;
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
x_117 = l_Lean_Elab_Term_expandAssert___closed__3;
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
x_126 = lean_box(2);
x_127 = l_Lean_Syntax_mkStrLit(x_95, x_126);
lean_dec(x_95);
x_128 = lean_array_push(x_125, x_127);
x_129 = l_term___x2b_x2b_____closed__2;
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = lean_array_push(x_101, x_130);
x_132 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
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
x_140 = l_myMacro____x40_Init_Notation___hyg_13918____closed__8;
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = lean_array_push(x_113, x_141);
x_143 = l_Lean_Parser_Term_panic___elambda__1___closed__2;
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = lean_array_push(x_110, x_144);
x_146 = l_termIfThenElse___closed__2;
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
x_150 = l_Lean_Parser_Term_notFollowedByRedefinedTermToken___elambda__1___closed__43;
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
x_159 = l_termDepIfThenElse___closed__24;
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
x_168 = l_Lean_Elab_Term_expandAssert___closed__3;
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
x_177 = lean_box(2);
x_178 = l_Lean_Syntax_mkStrLit(x_95, x_177);
lean_dec(x_95);
x_179 = lean_array_push(x_176, x_178);
x_180 = l_term___x2b_x2b_____closed__2;
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
x_182 = lean_array_push(x_152, x_181);
x_183 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
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
x_191 = l_myMacro____x40_Init_Notation___hyg_13918____closed__8;
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
x_193 = lean_array_push(x_164, x_192);
x_194 = l_Lean_Parser_Term_panic___elambda__1___closed__2;
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
x_196 = lean_array_push(x_161, x_195);
x_197 = l_termIfThenElse___closed__2;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_myMacro____x40_Init_Notation___hyg_2204____closed__2;
x_2 = l_Lean_Meta_assert___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandAssert___closed__2() {
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
x_3 = l___regBuiltin_Lean_Elab_Term_expandAssert___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_expandAssert___closed__2;
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
x_11 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_2, x_3);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
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
x_18 = l_Lean_Elab_Term_expandDbgTrace___closed__2;
x_19 = l_Lean_Elab_Term_expandDbgTrace___closed__5;
lean_inc(x_13);
x_20 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_19);
x_21 = l_Array_empty___closed__1;
x_22 = lean_array_push(x_21, x_20);
x_23 = l_prec_x28___x29___closed__3;
lean_inc(x_13);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_array_push(x_21, x_24);
x_26 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_23____closed__8;
x_27 = l_Lean_addMacroScope(x_15, x_26, x_14);
x_28 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_23____closed__7;
x_29 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_23____closed__13;
lean_inc(x_13);
x_30 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_29);
x_31 = lean_array_push(x_21, x_30);
x_32 = lean_array_push(x_21, x_5);
x_33 = l_Lean_nullKind___closed__2;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_array_push(x_31, x_34);
x_36 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_array_push(x_21, x_37);
x_39 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_40 = lean_array_push(x_38, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_array_push(x_25, x_41);
x_43 = l_prec_x28___x29___closed__7;
lean_inc(x_13);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_13);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_push(x_42, x_44);
x_46 = l_myMacro____x40_Init_Notation___hyg_13918____closed__8;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_array_push(x_21, x_47);
x_49 = l_myMacro____x40_Init_Notation___hyg_13918____closed__9;
lean_inc(x_13);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_13);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_array_push(x_21, x_50);
x_52 = l_myMacro____x40_Init_Notation___hyg_14520____closed__14;
lean_inc(x_13);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_13);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_array_push(x_21, x_53);
x_55 = l_myMacro____x40_Init_Notation___hyg_14520____closed__13;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_array_push(x_21, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_33);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_array_push(x_21, x_58);
x_60 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_13);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_array_push(x_59, x_61);
x_63 = lean_array_push(x_62, x_7);
x_64 = l_myMacro____x40_Init_Notation___hyg_13918____closed__12;
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = lean_array_push(x_51, x_65);
x_67 = l_myMacro____x40_Init_Notation___hyg_13918____closed__10;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_array_push(x_48, x_68);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_33);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_array_push(x_22, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_36);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_11, 0, x_72);
return x_11;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_73 = lean_ctor_get(x_11, 0);
x_74 = lean_ctor_get(x_11, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_11);
x_75 = lean_ctor_get(x_2, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_2, 1);
lean_inc(x_76);
lean_dec(x_2);
x_77 = l_Lean_Elab_Term_expandDbgTrace___closed__3;
lean_inc(x_75);
lean_inc(x_76);
x_78 = l_Lean_addMacroScope(x_76, x_77, x_75);
x_79 = l_Lean_Elab_Term_expandDbgTrace___closed__2;
x_80 = l_Lean_Elab_Term_expandDbgTrace___closed__5;
lean_inc(x_73);
x_81 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_81, 0, x_73);
lean_ctor_set(x_81, 1, x_79);
lean_ctor_set(x_81, 2, x_78);
lean_ctor_set(x_81, 3, x_80);
x_82 = l_Array_empty___closed__1;
x_83 = lean_array_push(x_82, x_81);
x_84 = l_prec_x28___x29___closed__3;
lean_inc(x_73);
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_73);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_array_push(x_82, x_85);
x_87 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_23____closed__8;
x_88 = l_Lean_addMacroScope(x_76, x_87, x_75);
x_89 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_23____closed__7;
x_90 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_23____closed__13;
lean_inc(x_73);
x_91 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_91, 0, x_73);
lean_ctor_set(x_91, 1, x_89);
lean_ctor_set(x_91, 2, x_88);
lean_ctor_set(x_91, 3, x_90);
x_92 = lean_array_push(x_82, x_91);
x_93 = lean_array_push(x_82, x_5);
x_94 = l_Lean_nullKind___closed__2;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = lean_array_push(x_92, x_95);
x_97 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_array_push(x_82, x_98);
x_100 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_101 = lean_array_push(x_99, x_100);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_94);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_array_push(x_86, x_102);
x_104 = l_prec_x28___x29___closed__7;
lean_inc(x_73);
x_105 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_105, 0, x_73);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_array_push(x_103, x_105);
x_107 = l_myMacro____x40_Init_Notation___hyg_13918____closed__8;
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = lean_array_push(x_82, x_108);
x_110 = l_myMacro____x40_Init_Notation___hyg_13918____closed__9;
lean_inc(x_73);
x_111 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_111, 0, x_73);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_array_push(x_82, x_111);
x_113 = l_myMacro____x40_Init_Notation___hyg_14520____closed__14;
lean_inc(x_73);
x_114 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_114, 0, x_73);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_array_push(x_82, x_114);
x_116 = l_myMacro____x40_Init_Notation___hyg_14520____closed__13;
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_118 = lean_array_push(x_82, x_117);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_94);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_array_push(x_82, x_119);
x_121 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_122 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_122, 0, x_73);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_array_push(x_120, x_122);
x_124 = lean_array_push(x_123, x_7);
x_125 = l_myMacro____x40_Init_Notation___hyg_13918____closed__12;
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = lean_array_push(x_112, x_126);
x_128 = l_myMacro____x40_Init_Notation___hyg_13918____closed__10;
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
x_130 = lean_array_push(x_109, x_129);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_94);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_array_push(x_83, x_131);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_97);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_74);
return x_134;
}
}
else
{
lean_object* x_135; uint8_t x_136; 
x_135 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_2, x_3);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = lean_ctor_get(x_2, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_2, 1);
lean_inc(x_139);
lean_dec(x_2);
x_140 = l_Lean_Elab_Term_expandDbgTrace___closed__3;
x_141 = l_Lean_addMacroScope(x_139, x_140, x_138);
x_142 = l_Lean_Elab_Term_expandDbgTrace___closed__2;
x_143 = l_Lean_Elab_Term_expandDbgTrace___closed__5;
lean_inc(x_137);
x_144 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_144, 0, x_137);
lean_ctor_set(x_144, 1, x_142);
lean_ctor_set(x_144, 2, x_141);
lean_ctor_set(x_144, 3, x_143);
x_145 = l_Array_empty___closed__1;
x_146 = lean_array_push(x_145, x_144);
x_147 = l_prec_x28___x29___closed__3;
lean_inc(x_137);
x_148 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_148, 0, x_137);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_array_push(x_145, x_148);
x_150 = l_termS_x21_____closed__3;
lean_inc(x_137);
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_137);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_array_push(x_145, x_151);
x_153 = lean_array_push(x_152, x_5);
x_154 = l_termS_x21_____closed__2;
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
x_156 = lean_array_push(x_145, x_155);
x_157 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_158 = lean_array_push(x_156, x_157);
x_159 = l_Lean_nullKind___closed__2;
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = lean_array_push(x_149, x_160);
x_162 = l_prec_x28___x29___closed__7;
lean_inc(x_137);
x_163 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_163, 0, x_137);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_array_push(x_161, x_163);
x_165 = l_myMacro____x40_Init_Notation___hyg_13918____closed__8;
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = lean_array_push(x_145, x_166);
x_168 = l_myMacro____x40_Init_Notation___hyg_13918____closed__9;
lean_inc(x_137);
x_169 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_169, 0, x_137);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_array_push(x_145, x_169);
x_171 = l_myMacro____x40_Init_Notation___hyg_14520____closed__14;
lean_inc(x_137);
x_172 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_172, 0, x_137);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_array_push(x_145, x_172);
x_174 = l_myMacro____x40_Init_Notation___hyg_14520____closed__13;
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_173);
x_176 = lean_array_push(x_145, x_175);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_159);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_array_push(x_145, x_177);
x_179 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_180 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_180, 0, x_137);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_array_push(x_178, x_180);
x_182 = lean_array_push(x_181, x_7);
x_183 = l_myMacro____x40_Init_Notation___hyg_13918____closed__12;
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
x_185 = lean_array_push(x_170, x_184);
x_186 = l_myMacro____x40_Init_Notation___hyg_13918____closed__10;
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_185);
x_188 = lean_array_push(x_167, x_187);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_159);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_array_push(x_146, x_189);
x_191 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
lean_ctor_set(x_135, 0, x_192);
return x_135;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_193 = lean_ctor_get(x_135, 0);
x_194 = lean_ctor_get(x_135, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_135);
x_195 = lean_ctor_get(x_2, 2);
lean_inc(x_195);
x_196 = lean_ctor_get(x_2, 1);
lean_inc(x_196);
lean_dec(x_2);
x_197 = l_Lean_Elab_Term_expandDbgTrace___closed__3;
x_198 = l_Lean_addMacroScope(x_196, x_197, x_195);
x_199 = l_Lean_Elab_Term_expandDbgTrace___closed__2;
x_200 = l_Lean_Elab_Term_expandDbgTrace___closed__5;
lean_inc(x_193);
x_201 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_201, 0, x_193);
lean_ctor_set(x_201, 1, x_199);
lean_ctor_set(x_201, 2, x_198);
lean_ctor_set(x_201, 3, x_200);
x_202 = l_Array_empty___closed__1;
x_203 = lean_array_push(x_202, x_201);
x_204 = l_prec_x28___x29___closed__3;
lean_inc(x_193);
x_205 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_205, 0, x_193);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_array_push(x_202, x_205);
x_207 = l_termS_x21_____closed__3;
lean_inc(x_193);
x_208 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_208, 0, x_193);
lean_ctor_set(x_208, 1, x_207);
x_209 = lean_array_push(x_202, x_208);
x_210 = lean_array_push(x_209, x_5);
x_211 = l_termS_x21_____closed__2;
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_210);
x_213 = lean_array_push(x_202, x_212);
x_214 = l_myMacro____x40_Init_Notation___hyg_1407____closed__8;
x_215 = lean_array_push(x_213, x_214);
x_216 = l_Lean_nullKind___closed__2;
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_215);
x_218 = lean_array_push(x_206, x_217);
x_219 = l_prec_x28___x29___closed__7;
lean_inc(x_193);
x_220 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_220, 0, x_193);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_array_push(x_218, x_220);
x_222 = l_myMacro____x40_Init_Notation___hyg_13918____closed__8;
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_221);
x_224 = lean_array_push(x_202, x_223);
x_225 = l_myMacro____x40_Init_Notation___hyg_13918____closed__9;
lean_inc(x_193);
x_226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_226, 0, x_193);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_array_push(x_202, x_226);
x_228 = l_myMacro____x40_Init_Notation___hyg_14520____closed__14;
lean_inc(x_193);
x_229 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_229, 0, x_193);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_array_push(x_202, x_229);
x_231 = l_myMacro____x40_Init_Notation___hyg_14520____closed__13;
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
x_233 = lean_array_push(x_202, x_232);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_216);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_array_push(x_202, x_234);
x_236 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_237 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_237, 0, x_193);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_array_push(x_235, x_237);
x_239 = lean_array_push(x_238, x_7);
x_240 = l_myMacro____x40_Init_Notation___hyg_13918____closed__12;
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
x_242 = lean_array_push(x_227, x_241);
x_243 = l_myMacro____x40_Init_Notation___hyg_13918____closed__10;
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_242);
x_245 = lean_array_push(x_224, x_244);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_216);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_array_push(x_203, x_246);
x_248 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_194);
return x_250;
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
static lean_object* _init_l_Lean_Elab_Term_elabSorry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declaration uses 'sorry'");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSorry___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabSorry___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSorry___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabSorry___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSorry___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkSorry___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSorry___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_mkSorry___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_elabSorry___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSorry___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSorry___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSorry___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabSorry___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSorry___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprBool___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSorry___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_instReprBool___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_elabSorry___closed__8;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabSorry___closed__10() {
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
static lean_object* _init_l_Lean_Elab_Term_elabSorry___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabSorry___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabSorry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_10 = l_Lean_Elab_Term_elabSorry___closed__3;
x_11 = 1;
x_12 = l_Lean_Elab_log___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__3(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_7, x_8, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_mkSorry___closed__2;
lean_inc(x_18);
lean_inc(x_21);
x_24 = l_Lean_addMacroScope(x_21, x_23, x_18);
x_25 = l_Lean_Elab_Term_elabSorry___closed__5;
x_26 = l_Lean_Elab_Term_elabSorry___closed__7;
lean_inc(x_15);
x_27 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_26);
x_28 = l_Array_empty___closed__1;
x_29 = lean_array_push(x_28, x_27);
x_30 = l_myMacro____x40_Init_Notation___hyg_14520____closed__14;
lean_inc(x_15);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_push(x_28, x_31);
x_33 = l_myMacro____x40_Init_Notation___hyg_14520____closed__13;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_array_push(x_28, x_34);
x_36 = l_Lean_setOptionFromString___closed__4;
x_37 = l_Lean_addMacroScope(x_21, x_36, x_18);
x_38 = l_Lean_Elab_Term_elabSorry___closed__9;
x_39 = l_Lean_Elab_Term_elabSorry___closed__11;
x_40 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_40, 0, x_15);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_39);
x_41 = lean_array_push(x_35, x_40);
x_42 = l_Lean_nullKind___closed__2;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_array_push(x_29, x_43);
x_45 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
lean_inc(x_46);
lean_inc(x_1);
x_47 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_47, 0, x_1);
lean_closure_set(x_47, 1, x_46);
lean_closure_set(x_47, 2, x_2);
x_48 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_46, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
return x_48;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSorry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSorry), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_17914____closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabSorry___closed__1;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_10 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Term_expandEmptyC___closed__7;
x_20 = l_Lean_addMacroScope(x_17, x_19, x_14);
x_21 = l_Lean_Elab_Term_expandEmptyC___closed__3;
x_22 = l_Lean_Elab_Term_expandEmptyC___closed__9;
x_23 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_22);
lean_inc(x_23);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_23);
lean_closure_set(x_24, 2, x_2);
x_25 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_23, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
return x_25;
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
x_13 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_myMacro____x40_Init_Notation___hyg_16227__expandListLit___spec__1(x_4, x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_4, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
x_18 = l_Lean_instQuoteProd___rarg___closed__2;
x_19 = l_Lean_addMacroScope(x_17, x_18, x_16);
x_20 = l_Lean_Elab_Term_mkPairs_loop___closed__3;
x_21 = l_Lean_Elab_Term_mkPairs_loop___closed__5;
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_19);
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
x_30 = l_myMacro____x40_Init_Notation___hyg_2204____closed__4;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_2 = x_10;
x_3 = x_31;
x_5 = x_15;
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
x_4 = l_myMacro____x40_Init_Notation___hyg_13918____closed__8;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 5);
x_5 = l_Lean_SourceInfo_fromRef(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
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
x_7 = l_myMacro____x40_Init_Notation___hyg_13918____closed__8;
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
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
x_51 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_935____closed__4;
x_52 = l_Lean_addMacroScope(x_43, x_51, x_4);
x_53 = lean_box(0);
x_54 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_935____closed__3;
x_55 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_52);
lean_ctor_set(x_55, 3, x_53);
lean_inc(x_55);
x_56 = lean_array_push(x_50, x_55);
lean_ctor_set(x_47, 1, x_56);
lean_ctor_set(x_47, 0, x_55);
return x_45;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_57 = lean_ctor_get(x_47, 0);
x_58 = lean_ctor_get(x_47, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_47);
x_59 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_935____closed__4;
x_60 = l_Lean_addMacroScope(x_43, x_59, x_4);
x_61 = lean_box(0);
x_62 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_935____closed__3;
x_63 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_60);
lean_ctor_set(x_63, 3, x_61);
lean_inc(x_63);
x_64 = lean_array_push(x_58, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_45, 0, x_65);
return x_45;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_66 = lean_ctor_get(x_45, 0);
x_67 = lean_ctor_get(x_45, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_45);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_70 = x_66;
} else {
 lean_dec_ref(x_66);
 x_70 = lean_box(0);
}
x_71 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_935____closed__4;
x_72 = l_Lean_addMacroScope(x_43, x_71, x_4);
x_73 = lean_box(0);
x_74 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_935____closed__3;
x_75 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_75, 0, x_68);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_75, 2, x_72);
lean_ctor_set(x_75, 3, x_73);
lean_inc(x_75);
x_76 = lean_array_push(x_69, x_75);
if (lean_is_scalar(x_70)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_70;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_67);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_79 = lean_ctor_get(x_3, 0);
x_80 = lean_ctor_get(x_3, 1);
x_81 = lean_ctor_get(x_3, 3);
x_82 = lean_ctor_get(x_3, 4);
x_83 = lean_ctor_get(x_3, 5);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_80);
x_84 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_80);
lean_ctor_set(x_84, 2, x_4);
lean_ctor_set(x_84, 3, x_81);
lean_ctor_set(x_84, 4, x_82);
lean_ctor_set(x_84, 5, x_83);
x_85 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__2(x_2, x_84, x_41);
lean_dec(x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_91 = x_86;
} else {
 lean_dec_ref(x_86);
 x_91 = lean_box(0);
}
x_92 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_935____closed__4;
x_93 = l_Lean_addMacroScope(x_80, x_92, x_4);
x_94 = lean_box(0);
x_95 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_935____closed__3;
x_96 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_96, 0, x_89);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_93);
lean_ctor_set(x_96, 3, x_94);
lean_inc(x_96);
x_97 = lean_array_push(x_90, x_96);
if (lean_is_scalar(x_91)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_91;
}
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
if (lean_is_scalar(x_88)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_88;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_87);
return x_99;
}
}
}
else
{
lean_object* x_100; uint8_t x_101; 
lean_dec(x_1);
x_100 = l_Lean_Parser_Term_cdot___elambda__1___closed__2;
x_101 = lean_name_eq(x_5, x_100);
if (x_101 == 0)
{
lean_object* x_102; size_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_array_get_size(x_6);
x_103 = lean_usize_of_nat(x_102);
lean_dec(x_102);
x_104 = x_6;
x_105 = lean_box_usize(x_103);
x_106 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___boxed__const__1;
x_107 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__1___boxed), 6, 3);
lean_closure_set(x_107, 0, x_105);
lean_closure_set(x_107, 1, x_106);
lean_closure_set(x_107, 2, x_104);
x_108 = x_107;
x_109 = lean_apply_3(x_108, x_2, x_3, x_4);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_115 = x_110;
} else {
 lean_dec_ref(x_110);
 x_115 = lean_box(0);
}
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_5);
lean_ctor_set(x_116, 1, x_113);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
if (lean_is_scalar(x_112)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_112;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_111);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_5);
x_119 = lean_ctor_get(x_109, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_109, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_121 = x_109;
} else {
 lean_dec_ref(x_109);
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
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_6);
lean_dec(x_5);
x_123 = lean_unsigned_to_nat(1u);
x_124 = lean_nat_add(x_4, x_123);
x_125 = lean_ctor_get(x_3, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_3, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_3, 3);
lean_inc(x_127);
x_128 = lean_ctor_get(x_3, 4);
lean_inc(x_128);
x_129 = lean_ctor_get(x_3, 5);
lean_inc(x_129);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_130 = x_3;
} else {
 lean_dec_ref(x_3);
 x_130 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_126);
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(0, 6, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_125);
lean_ctor_set(x_131, 1, x_126);
lean_ctor_set(x_131, 2, x_4);
lean_ctor_set(x_131, 3, x_127);
lean_ctor_set(x_131, 4, x_128);
lean_ctor_set(x_131, 5, x_129);
x_132 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_expandCDot___spec__2(x_2, x_131, x_124);
lean_dec(x_131);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_135 = x_132;
} else {
 lean_dec_ref(x_132);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_133, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_133, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_138 = x_133;
} else {
 lean_dec_ref(x_133);
 x_138 = lean_box(0);
}
x_139 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_935____closed__4;
x_140 = l_Lean_addMacroScope(x_126, x_139, x_4);
x_141 = lean_box(0);
x_142 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_935____closed__3;
x_143 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_143, 0, x_136);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_143, 2, x_140);
lean_ctor_set(x_143, 3, x_141);
lean_inc(x_143);
x_144 = lean_array_push(x_137, x_143);
if (lean_is_scalar(x_138)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_138;
}
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
if (lean_is_scalar(x_135)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_135;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_134);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_1);
lean_ctor_set(x_147, 1, x_2);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_4);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_3);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_1);
lean_ctor_set(x_149, 1, x_2);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_4);
return x_150;
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
x_13 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_113____spec__1(x_2, x_10);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_myMacro____x40_Init_Notation___hyg_13918____closed__9;
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
x_23 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_array_push(x_22, x_24);
x_26 = lean_array_push(x_25, x_11);
x_27 = l_myMacro____x40_Init_Notation___hyg_13918____closed__12;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_array_push(x_18, x_28);
x_30 = l_myMacro____x40_Init_Notation___hyg_13918____closed__10;
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
x_35 = l_myMacro____x40_Init_Notation___hyg_13918____closed__9;
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
x_42 = l_myMacro____x40_Init_Notation___hyg_13918____closed__13;
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_array_push(x_41, x_43);
x_45 = lean_array_push(x_44, x_11);
x_46 = l_myMacro____x40_Init_Notation___hyg_13918____closed__12;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_array_push(x_37, x_47);
x_49 = l_myMacro____x40_Init_Notation___hyg_13918____closed__10;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_22 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
x_24 = l_Lean_throwError___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__2(x_2, x_3, x_4, x_5, x_6, x_23, x_8, x_9);
lean_dec(x_23);
return x_24;
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
lean_object* x_10; lean_object* x_11; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_18 = lean_st_ref_get(x_8, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_7, 3);
lean_inc(x_22);
x_23 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 2);
lean_inc(x_27);
x_28 = lean_st_ref_get(x_8, x_25);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_21);
x_32 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_32, 0, x_21);
x_33 = x_32;
x_34 = lean_environment_main_module(x_21);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_24);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set(x_35, 4, x_27);
lean_ctor_set(x_35, 5, x_22);
lean_inc(x_1);
x_36 = l_Lean_Elab_Term_expandCDot_x3f(x_1, x_35, x_31);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_st_ref_take(x_8, x_30);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_40, 1);
lean_dec(x_43);
lean_ctor_set(x_40, 1, x_38);
x_44 = lean_st_ref_set(x_8, x_40, x_41);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_10 = x_37;
x_11 = x_45;
goto block_17;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_40, 0);
x_47 = lean_ctor_get(x_40, 2);
x_48 = lean_ctor_get(x_40, 3);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_40);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_38);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set(x_49, 3, x_48);
x_50 = lean_st_ref_set(x_8, x_49, x_41);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_10 = x_37;
x_11 = x_51;
goto block_17;
}
}
else
{
lean_object* x_52; 
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_36, 0);
lean_inc(x_52);
lean_dec(x_36);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Lean_throwErrorAt___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__1(x_53, x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_53);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
lean_object* x_62; uint8_t x_63; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_62 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot___spec__3___rarg(x_30);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
return x_62;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_62);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
block_17:
{
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_12; lean_object* x_13; 
x_12 = 1;
x_13 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_12, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
lean_inc(x_14);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_2);
x_16 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_16;
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
lean_object* l_Lean_Elab_Term_elabParen___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_4, 3);
lean_inc(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_4, 3, x_14);
x_15 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_4, 2);
x_19 = lean_ctor_get(x_4, 3);
x_20 = lean_ctor_get(x_4, 4);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*8);
x_22 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 1);
x_23 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 2);
x_24 = lean_ctor_get(x_4, 5);
x_25 = lean_ctor_get(x_4, 6);
x_26 = lean_ctor_get(x_4, 7);
x_27 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
lean_inc(x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_19);
x_30 = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_17);
lean_ctor_set(x_30, 2, x_18);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_30, 4, x_20);
lean_ctor_set(x_30, 5, x_24);
lean_ctor_set(x_30, 6, x_25);
lean_ctor_set(x_30, 7, x_26);
lean_ctor_set_uint8(x_30, sizeof(void*)*8, x_21);
lean_ctor_set_uint8(x_30, sizeof(void*)*8 + 1, x_22);
lean_ctor_set_uint8(x_30, sizeof(void*)*8 + 2, x_23);
lean_ctor_set_uint8(x_30, sizeof(void*)*8 + 3, x_27);
x_31 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot(x_2, x_3, x_30, x_5, x_6, x_7, x_8, x_9, x_10);
return x_31;
}
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
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabParen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_myMacro____x40_Init_Notation___hyg_13918____closed__8;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_Term_elabParen___closed__2;
x_13 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_119; uint8_t x_120; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_119 = l_Lean_nullKind___closed__2;
lean_inc(x_15);
x_120 = l_Lean_Syntax_isOfKind(x_15, x_119);
if (x_120 == 0)
{
lean_object* x_121; 
x_121 = lean_box(0);
x_16 = x_121;
goto block_118;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_122 = l_Lean_Syntax_getArgs(x_15);
x_123 = lean_array_get_size(x_122);
lean_dec(x_122);
x_124 = lean_unsigned_to_nat(0u);
x_125 = lean_nat_dec_eq(x_123, x_124);
lean_dec(x_123);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = lean_box(0);
x_16 = x_126;
goto block_118;
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_127 = l_Lean_instToExprUnit___lambda__1___closed__3;
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_9);
return x_128;
}
}
block_118:
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_16);
x_17 = l_Lean_nullKind___closed__2;
lean_inc(x_15);
x_18 = l_Lean_Syntax_isOfKind(x_15, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_Elab_Term_elabParen___closed__2;
x_20 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = l_Lean_Syntax_getArgs(x_15);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_25 = l_Lean_Elab_Term_elabParen___closed__2;
x_26 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_41; 
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_Syntax_getArg(x_15, x_27);
x_29 = l_Lean_Syntax_getArg(x_15, x_14);
lean_dec(x_15);
lean_inc(x_29);
x_41 = l_Lean_Syntax_isOfKind(x_29, x_17);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_1);
x_42 = lean_box(0);
x_30 = x_42;
goto block_40;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = l_Lean_Syntax_getArgs(x_29);
x_44 = lean_array_get_size(x_43);
lean_dec(x_43);
x_45 = lean_nat_dec_eq(x_44, x_14);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_1);
x_46 = lean_box(0);
x_30 = x_46;
goto block_40;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = l_Lean_Syntax_getArg(x_29, x_27);
lean_dec(x_29);
x_48 = l_myMacro____x40_Init_Notation___hyg_15440____closed__8;
lean_inc(x_47);
x_49 = l_Lean_Syntax_isOfKind(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = l_Lean_Parser_Term_tupleTail___elambda__1___closed__2;
lean_inc(x_47);
x_51 = l_Lean_Syntax_isOfKind(x_47, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_47);
lean_dec(x_28);
lean_dec(x_2);
lean_dec(x_1);
x_52 = l_Lean_Elab_Term_elabParen___closed__2;
x_53 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_54 = l_Lean_Syntax_getArg(x_47, x_14);
lean_dec(x_47);
x_55 = l_Lean_Syntax_getArgs(x_54);
lean_dec(x_54);
x_56 = l_Lean_mkOptionalNode___closed__2;
x_57 = lean_array_push(x_56, x_28);
x_58 = l_Lean_Syntax_SepArray_getElems___rarg(x_55);
lean_dec(x_55);
x_59 = l_Array_append___rarg(x_57, x_58);
lean_dec(x_58);
x_60 = lean_st_ref_get(x_8, x_9);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_7, 3);
lean_inc(x_64);
x_65 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_62);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_7, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_7, 2);
lean_inc(x_69);
x_70 = lean_st_ref_get(x_8, x_67);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
lean_inc(x_63);
x_74 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_74, 0, x_63);
x_75 = x_74;
x_76 = lean_environment_main_module(x_63);
x_77 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_66);
lean_ctor_set(x_77, 3, x_68);
lean_ctor_set(x_77, 4, x_69);
lean_ctor_set(x_77, 5, x_64);
x_78 = l_Lean_Elab_Term_mkPairs(x_59, x_77, x_73);
lean_dec(x_59);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_st_ref_take(x_8, x_72);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_82, 1);
lean_dec(x_85);
lean_ctor_set(x_82, 1, x_80);
x_86 = lean_st_ref_set(x_8, x_82, x_83);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
lean_inc(x_79);
lean_inc(x_1);
x_88 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabParen___lambda__1), 10, 3);
lean_closure_set(x_88, 0, x_1);
lean_closure_set(x_88, 1, x_79);
lean_closure_set(x_88, 2, x_2);
x_89 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_79, x_88, x_3, x_4, x_5, x_6, x_7, x_8, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = lean_ctor_get(x_82, 0);
x_91 = lean_ctor_get(x_82, 2);
x_92 = lean_ctor_get(x_82, 3);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_82);
x_93 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_80);
lean_ctor_set(x_93, 2, x_91);
lean_ctor_set(x_93, 3, x_92);
x_94 = lean_st_ref_set(x_8, x_93, x_83);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
lean_inc(x_79);
lean_inc(x_1);
x_96 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabParen___lambda__1), 10, 3);
lean_closure_set(x_96, 0, x_1);
lean_closure_set(x_96, 1, x_79);
lean_closure_set(x_96, 2, x_2);
x_97 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_1, x_79, x_96, x_3, x_4, x_5, x_6, x_7, x_8, x_95);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; 
lean_dec(x_2);
lean_dec(x_1);
x_98 = l_Lean_Syntax_getArg(x_47, x_14);
lean_dec(x_47);
x_99 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabType), 8, 1);
lean_closure_set(x_99, 0, x_98);
x_100 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_101 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_99, x_100, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_102);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_104);
x_105 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot(x_28, x_104, x_3, x_4, x_5, x_6, x_7, x_8, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_box(0);
x_109 = l_Lean_Elab_Term_ensureHasType(x_104, x_106, x_108, x_3, x_4, x_5, x_6, x_7, x_8, x_107);
return x_109;
}
else
{
uint8_t x_110; 
lean_dec(x_104);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_110 = !lean_is_exclusive(x_105);
if (x_110 == 0)
{
return x_105;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_105, 0);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_105);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_114 = !lean_is_exclusive(x_101);
if (x_114 == 0)
{
return x_101;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_101, 0);
x_116 = lean_ctor_get(x_101, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_101);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
block_40:
{
uint8_t x_31; 
lean_dec(x_30);
lean_inc(x_29);
x_31 = l_Lean_Syntax_isOfKind(x_29, x_17);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_2);
x_32 = l_Lean_Elab_Term_elabParen___closed__2;
x_33 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = l_Lean_Syntax_getArgs(x_29);
lean_dec(x_29);
x_35 = lean_array_get_size(x_34);
lean_dec(x_34);
x_36 = lean_nat_dec_eq(x_35, x_27);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_28);
lean_dec(x_2);
x_37 = l_Lean_Elab_Term_elabParen___closed__2;
x_38 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = l___private_Lean_Elab_BuiltinNotation_0__Lean_Elab_Term_elabCDot(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_39;
}
}
}
}
}
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
x_3 = l_myMacro____x40_Init_Notation___hyg_13918____closed__8;
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
lean_object* l_Lean_Elab_Term_elabSubst___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_10 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2);
x_11 = lean_array_push(x_10, x_2);
x_12 = lean_expr_instantiate1(x_1, x_2);
lean_dec(x_2);
x_13 = 0;
x_14 = 1;
x_15 = l_Lean_Meta_mkLambdaFVars(x_11, x_12, x_13, x_14, x_5, x_6, x_7, x_8, x_9);
return x_15;
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
x_16 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(x_2, x_15, x_3, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
x_19 = l_Lean_Meta_mkEqSymm(x_4, x_9, x_10, x_11, x_12, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_mkEqNDRec(x_17, x_5, x_20, x_9, x_10, x_11, x_12, x_21);
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
lean_object* x_17; lean_object* x_18; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
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
x_38 = lean_ctor_get(x_14, 6);
lean_inc(x_38);
x_39 = lean_ctor_get(x_14, 7);
lean_inc(x_39);
x_40 = l_Lean_replaceRef(x_3, x_35);
lean_dec(x_35);
x_41 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_41, 0, x_32);
lean_ctor_set(x_41, 1, x_33);
lean_ctor_set(x_41, 2, x_34);
lean_ctor_set(x_41, 3, x_40);
lean_ctor_set(x_41, 4, x_36);
lean_ctor_set(x_41, 5, x_37);
lean_ctor_set(x_41, 6, x_38);
lean_ctor_set(x_41, 7, x_39);
x_42 = 1;
lean_inc(x_15);
lean_inc(x_41);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_31);
x_43 = l_Lean_Elab_Term_elabTerm(x_3, x_31, x_42, x_42, x_10, x_11, x_12, x_13, x_41, x_15, x_16);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_15);
lean_inc(x_41);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_44);
x_46 = l_Lean_Elab_Term_ensureHasType(x_31, x_44, x_4, x_10, x_11, x_12, x_13, x_41, x_15, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_30);
lean_dec(x_6);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_17 = x_47;
x_18 = x_48;
goto block_29;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
lean_inc(x_15);
lean_inc(x_41);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_44);
x_51 = l_Lean_Meta_inferType(x_44, x_12, x_13, x_41, x_15, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_box(0);
lean_inc(x_15);
lean_inc(x_41);
lean_inc(x_13);
lean_inc(x_12);
x_55 = l_Lean_Meta_kabstract(x_52, x_6, x_54, x_12, x_13, x_41, x_15, x_53);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
x_59 = l_Lean_Expr_hasLooseBVars(x_57);
if (x_59 == 0)
{
lean_dec(x_57);
lean_dec(x_44);
lean_dec(x_41);
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
lean_ctor_set_tag(x_55, 1);
lean_ctor_set(x_55, 0, x_49);
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_free_object(x_55);
x_60 = lean_box(0);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_61 = l_Lean_Elab_Term_elabSubst___lambda__3(x_57, x_5, x_30, x_49, x_1, x_2, x_7, x_44, x_60, x_10, x_11, x_12, x_13, x_41, x_15, x_58);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_17 = x_62;
x_18 = x_63;
goto block_29;
}
else
{
uint8_t x_64; 
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
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_61, 0);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_61);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_55, 0);
x_69 = lean_ctor_get(x_55, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_55);
x_70 = l_Lean_Expr_hasLooseBVars(x_68);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_68);
lean_dec(x_44);
lean_dec(x_41);
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
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_49);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_box(0);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_73 = l_Lean_Elab_Term_elabSubst___lambda__3(x_68, x_5, x_30, x_49, x_1, x_2, x_7, x_44, x_72, x_10, x_11, x_12, x_13, x_41, x_15, x_69);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_17 = x_74;
x_18 = x_75;
goto block_29;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
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
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_78 = x_73;
} else {
 lean_dec_ref(x_73);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_49);
lean_dec(x_44);
lean_dec(x_41);
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
x_80 = !lean_is_exclusive(x_55);
if (x_80 == 0)
{
return x_55;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_55, 0);
x_82 = lean_ctor_get(x_55, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_55);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_49);
lean_dec(x_44);
lean_dec(x_41);
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
x_84 = !lean_is_exclusive(x_51);
if (x_84 == 0)
{
return x_51;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_51, 0);
x_86 = lean_ctor_get(x_51, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_51);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_41);
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
x_88 = !lean_is_exclusive(x_43);
if (x_88 == 0)
{
return x_43;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_43, 0);
x_90 = lean_ctor_get(x_43, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_43);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
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
x_21 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(x_1, x_20, x_2, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_mkEqNDRec(x_22, x_17, x_7, x_12, x_13, x_14, x_15, x_23);
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
x_14 = l_Lean_Meta_mkEqSymm(x_5, x_9, x_10, x_11, x_12, x_13);
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
x_32 = l_Lean_Elab_Term_elabTerm(x_18, x_30, x_31, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
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
x_47 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7;
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
x_65 = l_Lean_Meta_kabstract(x_12, x_59, x_64, x_5, x_6, x_7, x_8, x_63);
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
x_70 = l_Lean_Meta_kabstract(x_12, x_58, x_64, x_5, x_6, x_7, x_8, x_67);
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
x_18 = l_Lean_Elab_Term_elabTerm(x_2, x_16, x_17, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
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
x_31 = l_Lean_Meta_mkAppM(x_30, x_29, x_6, x_7, x_8, x_9, x_26);
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
x_41 = l_Lean_Meta_mkAppM(x_40, x_39, x_6, x_7, x_8, x_9, x_35);
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
lean_object* l_Lean_Elab_Term_elabNoindex(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = 1;
x_13 = l_Lean_Elab_Term_elabTerm(x_11, x_2, x_12, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabNoindex___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabNoindex(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNoindex___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNoindex___boxed), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabNoindex(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_noindex___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabNoindex___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Init_Data_ToString(lean_object*);
lean_object* initialize_Lean_Compiler_BorrowedAnnotation(lean_object*);
lean_object* initialize_Lean_Meta_KAbstract(lean_object*);
lean_object* initialize_Lean_Meta_Transform(lean_object*);
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
res = initialize_Lean_Meta_Transform(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__1 = _init_l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__1);
l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__2 = _init_l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__2);
l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__3 = _init_l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__3);
l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__4 = _init_l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__4);
l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__5 = _init_l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__5);
l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__6 = _init_l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___lambda__3___closed__6);
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
l_Lean_Elab_Term_elabAnonymousCtor___closed__8 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__8);
l_Lean_Elab_Term_elabAnonymousCtor___closed__9 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__9);
l_Lean_Elab_Term_elabAnonymousCtor___closed__10 = _init_l_Lean_Elab_Term_elabAnonymousCtor___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_elabAnonymousCtor___closed__10);
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
l___regBuiltin_Lean_Elab_Term_expandShow___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandShow___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandShow___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandShow(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandHave___lambda__1___closed__1 = _init_l_Lean_Elab_Term_expandHave___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandHave___lambda__1___closed__1);
l_Lean_Elab_Term_expandHave___lambda__1___closed__2 = _init_l_Lean_Elab_Term_expandHave___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandHave___lambda__1___closed__2);
l_Lean_Elab_Term_expandHave___lambda__1___closed__3 = _init_l_Lean_Elab_Term_expandHave___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandHave___lambda__1___closed__3);
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
l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1___closed__1 = _init_l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1___closed__1);
l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1___closed__2 = _init_l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLeadingParserMacro___lambda__1___closed__2);
l_Lean_Elab_Term_elabLeadingParserMacro___closed__1 = _init_l_Lean_Elab_Term_elabLeadingParserMacro___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLeadingParserMacro___closed__1);
l___regBuiltin_Lean_Elab_Term_elabLeadingParserMacro___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabLeadingParserMacro___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLeadingParserMacro___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabLeadingParserMacro(lean_io_mk_world());
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
l_Lean_Elab_Term_elabTrailingParserMacro___lambda__1___closed__1 = _init_l_Lean_Elab_Term_elabTrailingParserMacro___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabTrailingParserMacro___lambda__1___closed__1);
l_Lean_Elab_Term_elabTrailingParserMacro___closed__1 = _init_l_Lean_Elab_Term_elabTrailingParserMacro___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabTrailingParserMacro___closed__1);
l___regBuiltin_Lean_Elab_Term_elabTrailingParserMacro___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabTrailingParserMacro___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTrailingParserMacro___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabTrailingParserMacro(lean_io_mk_world());
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
l___regBuiltin_Lean_Elab_Term_expandAssert___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandAssert___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandAssert___closed__1);
l___regBuiltin_Lean_Elab_Term_expandAssert___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_expandAssert___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandAssert___closed__2);
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
l_Lean_Elab_Term_elabSorry___closed__1 = _init_l_Lean_Elab_Term_elabSorry___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabSorry___closed__1);
l_Lean_Elab_Term_elabSorry___closed__2 = _init_l_Lean_Elab_Term_elabSorry___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabSorry___closed__2);
l_Lean_Elab_Term_elabSorry___closed__3 = _init_l_Lean_Elab_Term_elabSorry___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabSorry___closed__3);
l_Lean_Elab_Term_elabSorry___closed__4 = _init_l_Lean_Elab_Term_elabSorry___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabSorry___closed__4);
l_Lean_Elab_Term_elabSorry___closed__5 = _init_l_Lean_Elab_Term_elabSorry___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabSorry___closed__5);
l_Lean_Elab_Term_elabSorry___closed__6 = _init_l_Lean_Elab_Term_elabSorry___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabSorry___closed__6);
l_Lean_Elab_Term_elabSorry___closed__7 = _init_l_Lean_Elab_Term_elabSorry___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_elabSorry___closed__7);
l_Lean_Elab_Term_elabSorry___closed__8 = _init_l_Lean_Elab_Term_elabSorry___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_elabSorry___closed__8);
l_Lean_Elab_Term_elabSorry___closed__9 = _init_l_Lean_Elab_Term_elabSorry___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_elabSorry___closed__9);
l_Lean_Elab_Term_elabSorry___closed__10 = _init_l_Lean_Elab_Term_elabSorry___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_elabSorry___closed__10);
l_Lean_Elab_Term_elabSorry___closed__11 = _init_l_Lean_Elab_Term_elabSorry___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_elabSorry___closed__11);
l___regBuiltin_Lean_Elab_Term_elabSorry___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabSorry___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSorry___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabSorry(lean_io_mk_world());
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
l___regBuiltin_Lean_Elab_Term_elabNoindex___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabNoindex___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNoindex___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabNoindex(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
