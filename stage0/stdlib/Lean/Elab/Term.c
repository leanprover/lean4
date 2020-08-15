// Lean compiler output
// Module: Lean.Elab.Term
// Imports: Init Lean.Util.Sorry Lean.Structure Lean.Meta.ExprDefEq Lean.Meta.AppBuilder Lean.Meta.SynthInstance Lean.Meta.Tactic.Util Lean.Hygiene Lean.Util.RecDepth Lean.Elab.Log Lean.Elab.Alias Lean.Elab.ResolveName Lean.Elab.Level
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
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Term_throwError___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLevelNames(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__4;
lean_object* l_Lean_Elab_Term_elabChar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_6__isTypeApp_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
uint8_t l___private_Lean_Elab_Term_4__hasCDot(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabImplicitLambdaAux___closed__2;
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__1;
lean_object* l_Lean_mkAppStx(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadQuotation;
lean_object* l_Lean_Elab_Term_elabRawNumLit___closed__1;
extern lean_object* l_Lean_Closure_mkNewLevelParam___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__1;
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__8;
uint8_t l_Lean_MessageData_hasSyntheticSorry___main(lean_object*);
lean_object* l_Lean_Elab_Term_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabImplicitLambdaAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabStr(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Term_14__isLambdaWithImplicit___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabImplicitLambdaAux___closed__1;
lean_object* l_Lean_Elab_Term_elabRawStrLit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkTermElabAttribute___closed__4;
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
extern lean_object* l_Lean_Parser_Term_explicit___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_State_inhabited;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_20__resolveLocalNameAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__9;
lean_object* l_Lean_Elab_Term_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_HasQuote___closed__2;
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabHole___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadLog___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkTermElabAttribute___closed__8;
lean_object* l_Lean_Elab_Term_isDefEqNoConstantApprox(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_Term_tryPostpone___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkTermElabAttribute___closed__7;
lean_object* l_Lean_Elab_Term_assignExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabUsingElabFns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkTermElabAttribute___closed__3;
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__2;
extern lean_object* l_IO_Prim_fopenFlags___closed__12;
lean_object* l_Lean_Elab_Term_throwErrorIfErrors___closed__1;
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCacheWhen(lean_object*);
lean_object* l_Lean_Elab_Term_monadLog___closed__3;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getDeclName_x3f(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabTacticBlock(lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshId(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__10;
lean_object* l_Lean_Elab_Term_elabParen(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Elab_Term_monadLog___spec__1(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__1;
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandArrayLit___closed__7;
lean_object* l_Lean_Elab_Term_getLocalInsts___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCacheWhen___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_15__tryCoeSort___closed__7;
uint8_t l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__5;
extern lean_object* l_Lean_Parser_Term_type___elambda__1___closed__2;
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l___private_Lean_Elab_Term_22__mkFreshLevelMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabUsingElabFns___closed__2;
lean_object* l_Lean_Elab_Term_elabQuotedName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MacroScopesView_format(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_setMCtx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__11;
lean_object* l_Lean_mkMVar(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_throwError___spec__2(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkSorry___closed__4;
lean_object* l_Lean_Elab_Term_tryCoe___closed__2;
lean_object* l_Lean_Elab_Term_resolveName___closed__3;
lean_object* l___private_Lean_Elab_Term_20__resolveLocalNameAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_logTrace___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__2;
lean_object* l_Lean_Elab_Term_elabTypeStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Term_elabUsingElabFns___spec__2(lean_object*, lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNum___closed__1;
lean_object* l_Lean_Elab_Term_getEnv___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_throwErrorIfErrors___closed__2;
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
extern lean_object* l_Lean_charLitKind___closed__2;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_mkAppTypeMismatchMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___rarg___closed__1;
lean_object* l_Lean_Elab_Term_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__6;
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__6;
lean_object* l_Lean_Elab_Term_getDecLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadQuotation___closed__2;
lean_object* l_Lean_Meta_instantiateLevelMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__3;
lean_object* l_Lean_Elab_Term_withoutPostponing(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__13;
lean_object* l_Lean_Elab_Term_decLevel(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_15__tryCoeSort(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_compileDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabRawStrLit___closed__2;
lean_object* l_Lean_Elab_Term_elabParen___closed__3;
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_compileDecl___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Literal_type___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Term_mkAuxName___closed__3;
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache(lean_object*);
lean_object* l_Lean_Elab_Term_mkForallUsedOnly(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadLog___closed__7;
lean_object* l___private_Lean_Elab_Term_18__mkPairsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabProp(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toStr___closed__1;
lean_object* l_Lean_Elab_Term_ensureType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBadCDot___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_15__tryCoeSort___closed__3;
extern lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabParen(lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Elab_Term_logTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__1;
lean_object* l___private_Lean_Elab_Term_21__resolveLocalName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isTypeFormer(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withIncRecDepth(lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkAuxName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabRawCharLit(lean_object*);
lean_object* l_Lean_Elab_Term_elabRawNumLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__3;
extern lean_object* l_Lean_unitToExpr___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Term_18__mkPairsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_typeAscription___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwError(lean_object*);
lean_object* l_Lean_Elab_Term_elabSort___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMCtx(lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Elab_Term_withLCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_15__tryCoeSort___closed__5;
lean_object* l_Lean_Elab_Term_synthesizeInst(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__3;
lean_object* l_Lean_Elab_Term_monadLog___closed__10;
lean_object* l_Lean_Elab_Term_resolveName___closed__6;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
extern lean_object* l_Lean_Parser_Term_tupleTail___elambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx(lean_object*);
lean_object* l_Lean_Elab_Term_dbgTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabRawStrLit___closed__3;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLetDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_Exception_hasToString(lean_object*);
lean_object* l_Lean_Elab_Term_mkTermElabAttribute___closed__5;
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
extern lean_object* l_Lean_listToExpr___rarg___closed__4;
lean_object* l_Lean_Elab_Term_resolveName___closed__5;
lean_object* l_Lean_Elab_Term_mkFreshExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_LVal_hasToString(lean_object*);
lean_object* l_Lean_Elab_Term_elabImplicitLambda___main(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__7;
lean_object* l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__2;
lean_object* l_Lean_Elab_Term_trace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l_Lean_Elab_Term_MetaHasEval___rarg___closed__6;
extern lean_object* l_Lean_levelZero;
lean_object* l_Lean_Elab_Term_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabResult_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_expandCDot_x3f___closed__4;
lean_object* l___private_Lean_Elab_Term_3__fromMetaState(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabUsingElabFns___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppGoal(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__1;
lean_object* l_Lean_Elab_Term_termElabAttribute___closed__2;
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getTraceState(lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__1;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Syntax_foldSepRevArgsM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshTypeMVar(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_9__exceptionToSorry(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAux___main___closed__1;
lean_object* l_Lean_Elab_Term_withConfig(lean_object*);
lean_object* l___private_Lean_Elab_Term_7__isMonad_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBadCDot___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshAnonymousIdent(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabParen___closed__2;
lean_object* l_Lean_Elab_Term_mkLet(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabImplicitLambdaAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadLog___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_7__isMonad_x3f___closed__1;
lean_object* l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__3;
lean_object* l_Lean_Elab_Term_elabParen___closed__1;
lean_object* l_Lean_Elab_Term_addDecl(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_24__regTraceClasses___closed__1;
lean_object* l___private_Lean_Elab_Term_15__tryCoeSort___closed__1;
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_liftMetaM(lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l___private_Lean_Elab_Term_7__isMonad_x3f___closed__2;
lean_object* l_Lean_Elab_Term_isTypeFormerType(lean_object*, lean_object*, lean_object*);
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
lean_object* l_Lean_Meta_isClass(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabHole(lean_object*);
lean_object* l_Lean_Elab_Term_withTransparency(lean_object*);
extern lean_object* l_Lean_Parser_Term_byTactic___elambda__1___closed__2;
extern lean_object* l_Lean_Meta_run___rarg___closed__5;
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withConfig___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryCoe___closed__4;
lean_object* l_Lean_mkAuxDefinition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Term_mkFreshAnonymousName___boxed(lean_object*);
extern lean_object* l_Lean_Meta_dbgTrace___rarg___closed__1;
lean_object* l_Lean_Elab_Term_monadLog___closed__5;
extern lean_object* l_Lean_Parser_termParser___closed__1;
lean_object* l_Lean_Elab_Term_tryCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_17__elabOptLevel___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__3;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_sort___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_throwErrorAt(lean_object*);
lean_object* l_Lean_Elab_Term_elabLevel(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedHole(lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadLog___closed__1;
lean_object* l___private_Lean_Elab_Term_18__mkPairsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object*);
lean_object* l_Array_isEqvAux___main___at_Lean_Elab_Term_withMVarContext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Term_3__fromMetaState___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__5;
lean_object* l_Lean_Elab_Term_elabRawCharLit(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__3;
lean_object* l_Std_PersistentArray_foldlMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshAnonymousName___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_MetaHasEval___rarg___closed__2;
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
lean_object* l_Lean_Elab_Term_throwErrorAt___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withMVarContext(lean_object*);
lean_object* l_Lean_Elab_Term_termElabAttribute___closed__4;
lean_object* l_Lean_Elab_Term_addContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Term_14__isLambdaWithImplicit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabByTactic(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_observing(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutMacroStackAtErr(lean_object*);
lean_object* l_Lean_Elab_Term_withMacroExpansion(lean_object*);
lean_object* l_Lean_Elab_Term_getTraceState___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_State_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_MetaHasEval___rarg___closed__4;
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_Lean_Elab_Term_dbgTrace(lean_object*);
lean_object* l_Lean_Elab_Term_decLevel_x3f(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l_Lean_Elab_Term_elabTermWithoutImplicitLambdas(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshFVarId___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_getLevel(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryCoe___closed__1;
lean_object* l_Lean_Elab_Term_getCurrNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_monadLog___closed__8;
lean_object* l_Lean_Elab_Term_tryLiftAndCoe___closed__4;
lean_object* l_Lean_Elab_Term_isExprMVarAssigned___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabProp___rarg(lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l___private_Lean_Elab_Term_15__tryCoeSort___closed__2;
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Elab_Term_elabUsingElabFns___spec__6___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_23__mkConsts(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_termElabAttribute___closed__1;
lean_object* l___private_Lean_Elab_Term_5__expandCDot___main___closed__3;
lean_object* l_Lean_Elab_Term_mkFreshInstanceName(lean_object*);
lean_object* l_Lean_Elab_Term_elabChar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__3;
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Parser_Term_quotedName___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabByTactic___closed__2;
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__3;
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Term_5__expandCDot___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Term_14__isLambdaWithImplicit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkConst___closed__2;
lean_object* l_Lean_Elab_Term_isType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_setEnv___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_5__expandCDot___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabQuotedName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryLiftAndCoe___closed__1;
lean_object* l_Lean_Elab_Term_TermElabM_inhabited(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Term_3__fromMetaState___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInstMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTacticBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__1___closed__1;
lean_object* l_Lean_Elab_Term_withTransparency___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_lift___at_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabUsingElabFns___closed__4;
lean_object* l_Lean_Elab_Term_setTraceState___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__7;
lean_object* l_Lean_Elab_Term_elabTacticBlock___closed__1;
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__1___closed__2;
lean_object* l_Lean_Elab_Term_tryLiftAndCoe___closed__2;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_mkConst___closed__4;
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallUsedOnly(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNum(lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_Term_elabUsingElabFns___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_blockImplicitLambda___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_monadQuotation___closed__1;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Term_4__hasCDot___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkAuxDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_5__expandCDot___main___closed__2;
uint8_t l_Lean_Elab_Term_blockImplicitLambda(lean_object*);
lean_object* l_Lean_Elab_Term_elabTypeStx(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_assignLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabUsingElabFns___spec__3(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__3;
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadLog___closed__6;
extern lean_object* l_Lean_strLitKind___closed__2;
lean_object* l_Lean_Elab_Term_dropTermParens(lean_object*);
lean_object* l___private_Lean_Elab_Term_13__isExplicitApp___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_elabUsingElabFns___closed__1;
lean_object* l_Lean_Elab_Term_withFreshMacroScope(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__1;
lean_object* l_Lean_Elab_Term_resolveName___closed__7;
lean_object* l_Lean_Elab_Term_addDecl___boxed(lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAux___main(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_termElabAttribute___closed__3;
lean_object* l_Nat_repr(lean_object*);
lean_object* l___private_Lean_Elab_Term_14__isLambdaWithImplicit___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_State_inhabited___closed__2;
lean_object* l_Lean_Elab_Term_elabUsingElabFns___closed__6;
lean_object* l_Lean_Elab_Term_elabImplicitLambda(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwErrorIfErrors___closed__3;
lean_object* l_Lean_Elab_Term_getLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getMacros(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandCDot_x3f___closed__3;
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_namedHole___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__12;
lean_object* l_Lean_Elab_Term_trySynthInstance(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_liftLevelM___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabParen___closed__1;
lean_object* l_Lean_Elab_Term_elabRawStrLit___closed__1;
lean_object* l_Lean_Syntax_prettyPrint(lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter;
lean_object* l_Lean_Elab_Term_elabRawStrLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_Elab_Term_termElabAttribute___spec__2(lean_object*);
extern lean_object* l_Lean_Parser_Term_instBinder___elambda__1___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l___private_Lean_Elab_Term_10__postponeElabTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__5;
lean_object* l_Lean_Elab_Term_monadLog___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_fun___elambda__1___closed__2;
extern lean_object* l_Lean_Elab_Exception_hasToString___closed__1;
lean_object* l___private_Lean_Elab_Term_5__expandCDot___main___closed__1;
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabRawNumLit(lean_object*);
extern size_t l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Lean_Elab_Term_elabProp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withRef___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___main___at_Lean_Elab_Term_withLocalContext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_assignExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Term_22__mkFreshLevelMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLocalContext(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_applyResult___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadQuotation___closed__4;
lean_object* l_Lean_Elab_Term_withLocalDecl___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule(lean_object*);
extern lean_object* l_Lean_Meta_withIncRecDepth___rarg___closed__2;
lean_object* l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__4;
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkTermElabAttribute(lean_object*);
extern lean_object* l_Lean_numLitKind___closed__2;
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__4;
lean_object* l_Lean_Elab_Term_MetaHasEval___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTacticBlock___closed__2;
extern lean_object* l_Lean_Parser_Term_fun___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_monadLog___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkAppM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l_Lean_Meta_isTypeFormerType___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Elab_Term_expandArrayLit___closed__9;
lean_object* l_Lean_Elab_Term_useImplicitLambda_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshFVarId(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLevel___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
extern lean_object* l_Lean_charToExpr___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_expandCDot_x3f___closed__2;
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Term_elabUsingElabFns___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandArrayLit___closed__4;
lean_object* l_Lean_Elab_Term_elabImplicitLambda___main___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__2;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
lean_object* l_Lean_Elab_Term_liftLevelM(lean_object*);
lean_object* l_Lean_Elab_Term_elabProp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__8;
lean_object* l_Lean_Elab_addMacroStack(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_Elab_Term_elabTermAux(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_termElabAttribute___closed__5;
lean_object* l_Lean_Elab_Term_expandArrayLit___closed__8;
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabRawNumLit___closed__1;
lean_object* l_Lean_Meta_mkFreshId___rarg(lean_object*);
lean_object* l_Std_PersistentArray_foldlMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Term_throwError___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandListLit___closed__1;
lean_object* l_Lean_Elab_Term_getCurrNamespace___boxed(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
lean_object* l___private_Lean_Elab_Term_1__mkMessageAux(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Term_getLocalInsts(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshInstanceName___rarg(lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isClass(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabResult_inhabited;
lean_object* l_Lean_Elab_Term_withMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_expandListLit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Elab_Term_expandArrayLit___closed__1;
lean_object* l_Lean_Elab_Term_TermElabM_inhabited___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkPure(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
lean_object* l_Lean_Elab_Term_mkFreshAnonymousIdent___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabRawNumLit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Term_elabUsingElabFns___spec__1(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandListLit(lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l_Lean_Elab_Term_tryLiftAndCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_15__tryCoeSort___closed__4;
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_cdot___elambda__1___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabSort(lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__9;
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Elab_Term_elabUsingElabFns___spec__6(lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
extern lean_object* l_Lean_String_HasQuote___closed__2;
lean_object* l_Lean_Elab_Term_mkConst(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandArrayLit___closed__2;
lean_object* l_Lean_Elab_Term_mkConst___closed__3;
lean_object* l_Lean_Elab_Term_resolveName___closed__4;
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_throwError___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Term_14__isLambdaWithImplicit___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__2;
lean_object* l_Lean_Elab_Term_expandListLit___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNamedHole___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Elab_Term_expandCDot_x3f___closed__1;
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__2;
lean_object* l_Lean_Elab_Term_monadLog___closed__2;
extern lean_object* l_Lean_Meta_Exception_toStr___closed__7;
lean_object* l_Lean_Elab_Term_dropTermParens___main(lean_object*);
lean_object* l_Lean_Elab_Term_logDbgTrace___closed__1;
lean_object* l___private_Lean_Elab_Term_19__elabCDot(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getDeclName_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__10;
lean_object* l_Std_PersistentArray_forM___at___private_Lean_Parser_Module_4__testModuleParserAux___main___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__5;
lean_object* l___regBuiltin_Lean_Elab_Term_expandArrayLit(lean_object*);
lean_object* l_Lean_Elab_Term_logDbgTrace___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l_Lean_Elab_Term_mkTermElabAttribute___closed__9;
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Term_mkFreshAnonymousName(lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam_x27(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLCtx(lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
extern lean_object* l___private_Lean_Meta_Basic_12__regTraceClasses___closed__3;
lean_object* l_Lean_Elab_Term_withoutPostponing___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_prop___elambda__1___closed__2;
extern lean_object* l_Lean_prodToExpr___rarg___lambda__1___closed__4;
lean_object* l_Lean_Elab_Term_savingMCtx(lean_object*);
lean_object* l_Lean_Elab_Term_Exception_inhabited;
lean_object* l_Lean_Elab_Term_elabHole(lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedHole___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabRawStrLit(lean_object*);
lean_object* l_Lean_Elab_Term_withRef(lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__5;
lean_object* l___private_Lean_Elab_Term_10__postponeElabTerm___closed__2;
lean_object* l_Lean_Elab_Term_MetaHasEval___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Term_isLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_16__mkAuxNameAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBadCDot___rarg___closed__3;
lean_object* l_Lean_Elab_Term_setMCtx(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabStr(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Elab_Term_MetaHasEval___rarg___closed__1;
lean_object* l_Lean_mkLevelSucc(lean_object*);
lean_object* l_Lean_Elab_Term_getLCtx(lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_Term_4__hasCDot___main(lean_object*);
lean_object* l_Lean_Elab_Term_traceAtCmdPos(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Lean_Elab_Term_elabTacticBlock___closed__3;
extern lean_object* l_Std_PersistentArray_empty___closed__3;
lean_object* l_Lean_Elab_Term_withReducible(lean_object*);
lean_object* l_Lean_Elab_Term_elabUsingElabFns___closed__5;
lean_object* l_Lean_Elab_Term_TermElabM_inhabited___rarg(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Elab_Term_monadLog___closed__9;
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkConst___closed__5;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_getMaxRecDepth(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChar(lean_object*);
lean_object* l_Lean_Elab_Term_elabUsingElabFns(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_MetaHasEval___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabHole___closed__1;
lean_object* l_Lean_Syntax_isTermId_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Elab_Term_registerSyntheticMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Term_expandArrayLit(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabSort___closed__1;
lean_object* l___private_Lean_Elab_Term_4__hasCDot___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__9;
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withTransparency___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_assignLevelMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_Term_12__isExplicit(lean_object*);
lean_object* lean_metavar_ctx_assign_level(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_11__elabUsingElabFnsAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryLiftAndCoe___closed__6;
lean_object* l_Lean_Elab_Term_savingMCtx___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_object* l_Lean_Elab_Term_mkFreshFVarId___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_elabImplicitLambda___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNamedHole(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toExprAux___main(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot(lean_object*);
lean_object* l_Lean_Elab_Term_elabUsingElabFns___closed__3;
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withRef___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_Term_14__isLambdaWithImplicit(lean_object*);
extern lean_object* l_Lean_EnvExtension_setState___closed__1;
lean_object* l_Lean_Elab_Term_liftLevelM___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_modifyEnv(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_lift___at_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_whnfCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadLog___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l___private_Lean_Elab_Term_1__mkMessageAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCacheWhen___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_modifyEnv___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_logTrace___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Term_4__hasCDot___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveGlobalName___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_commitWhen___at___private_Lean_Meta_ExprDefEq_1__isDefEqEta___spec__1___closed__1;
lean_object* l_Lean_Elab_Term_expandArrayLit___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
lean_object* l_Lean_Elab_Term_mkConst___closed__1;
lean_object* l_Lean_Elab_Term_isExprMVarAssigned(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabHole___boxed(lean_object*);
extern lean_object* l___private_Lean_Meta_LevelDefEq_10__processPostponedStep___closed__1;
extern lean_object* l_Lean_Meta_evalNat___main___closed__8;
lean_object* l_Lean_Elab_Term_mkExplicitBinder(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSort(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_levelMVarToParam___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_16__mkAuxNameAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withMVarContext___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabImplicitLambda___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_evalNat___main___closed__7;
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Elab_Term_withIncRecDepth___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_4__hasCDot___main___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Elab_Term_whnfForall(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Term_8__tryPureCoe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getEnv(lean_object*);
lean_object* l_Lean_Elab_Term_getOpenDecls(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkTermIdFrom(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabRawCharLit___closed__1;
extern lean_object* l_Lean_FileMap_Inhabited___closed__1;
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_Elab_Term_logDbgTrace(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshExprMVarWithId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__12;
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshExprMVarWithId(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__3;
extern lean_object* l_Lean_KernelException_toMessageData___closed__12;
lean_object* l_Lean_Elab_Term_monadLog___closed__11;
lean_object* l_Lean_Elab_Term_mkTacticMVar___closed__2;
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_21__resolveLocalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__1;
uint8_t l___private_Lean_Elab_Term_13__isExplicitApp(lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Term_elabUsingElabFns___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabImplicitLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkTermElabAttribute___closed__6;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabByTactic___closed__3;
lean_object* l_Lean_Elab_Term_resolveGlobalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Term_throwError___spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOpenDecls___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getTraceState___boxed(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Term_23__mkConsts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLetDecl(lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandArrayLit___closed__1;
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__4;
lean_object* l_Lean_Elab_Term_withoutMacroStackAtErr___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCache___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l_Lean_Elab_Term_withLocalDecl(lean_object*);
lean_object* l_Lean_Elab_Term_elabByTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__2;
lean_object* l_Lean_Elab_Term_withLocalDecl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkPairs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__11;
lean_object* l_Lean_Elab_Term_getLevelNames___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLCtx___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabByTactic___closed__1;
lean_object* l_Lean_Elab_Term_ppGoal(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_setTraceState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostpone(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkPairs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwErrorIfErrors(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadLog___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkAuxDefinition(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_10__postponeElabTerm___closed__1;
lean_object* l___private_Lean_Elab_Term_15__tryCoeSort___closed__6;
lean_object* l_Lean_Elab_Term_monadQuotation___closed__3;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Term_22__mkFreshLevelMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_setEnv(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_arrayToExpr___rarg___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
lean_object* l_Lean_Elab_Term_elabTacticBlock(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Elab_Term_monadLog___lambda__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNum(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Unhygienic_run___rarg___closed__1;
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* l_Lean_Elab_Term_addContext(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_coeOfOptExpr___closed__1;
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabUsingElabFns___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_listLit___elambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabTacticBlock___closed__1;
uint8_t l_Lean_LocalInstance_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__1;
lean_object* l___private_Lean_Elab_Term_24__regTraceClasses(lean_object*);
lean_object* lean_compile_decl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache___boxed(lean_object*);
uint8_t l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Term_12__isExplicit___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__1;
lean_object* l_Lean_Elab_Term_elabRawCharLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChar___closed__1;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_mkTermElabAttribute___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMCtx___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_applyResult(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__2;
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_MetaHasEval___rarg___closed__3;
lean_object* l_Lean_Elab_Term_mkTacticMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabRawStrLit___closed__1;
lean_object* lean_usize_to_nat(size_t);
extern lean_object* l_Lean_Elab_mkMacroAttribute___closed__2;
lean_object* l_Lean_Elab_Term_expandArrayLit___closed__3;
uint8_t l_Array_isEqvAux___main___at_Lean_Elab_Term_withMVarContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_lift___at_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Message_toString(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_char___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isLocalTermId_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_Elab_Term_MetaHasEval___rarg___closed__5;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_Term_18__mkPairsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__8;
lean_object* l_Lean_Elab_Term_trace(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_Elab_Term_withLocalContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshInstanceName___boxed(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarWithId(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__2;
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__6;
lean_object* l___private_Lean_Elab_Term_2__fromMetaException(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__1;
lean_object* l_Lean_Elab_Term_resolveName___closed__1;
lean_object* l_Lean_Elab_Term_mkAuxName___closed__1;
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCache(lean_object*);
lean_object* l_Lean_Elab_Term_MetaHasEval(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_Inhabited___closed__1;
lean_object* l_Lean_Elab_Term_registerSyntheticMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withReducible___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateLevelMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasTypeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryLiftAndCoe___closed__5;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__1;
lean_object* l___private_Lean_Elab_Term_17__elabOptLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkTacticMVar___closed__1;
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_expandListLit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
extern lean_object* l_Lean_Meta_mkSorry___closed__2;
extern lean_object* l_EStateM_MonadState___closed__2;
extern lean_object* l_Lean_Parser_Term_arrayLit___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_getOptions___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryLiftAndCoe___closed__7;
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Term_throwError___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandListLit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadLog;
lean_object* l_Lean_Elab_Term_getMCtx___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__4;
lean_object* l_Lean_Elab_Term_monadLog___closed__4;
lean_object* l_Lean_Elab_Term_elabBadCDot___rarg___closed__1;
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_Term_elabUsingElabFns___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_liftMetaM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkTermElabAttribute___closed__1;
lean_object* l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__2;
lean_object* l_Lean_Elab_Term_elabTermWithoutImplicitLambdas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabUsingElabFns___spec__3___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_listToExpr___rarg___closed__6;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadLog___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isLocalTermId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandCDot_x3f(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
lean_object* l_Lean_Elab_Term_mkFreshTypeMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBadCDot___rarg___closed__2;
lean_object* l_Lean_Elab_Term_elabBadCDot(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_5__expandCDot(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkAuxName___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabStr___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_IO_println___at_IO_runMeta___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__6;
lean_object* l_Lean_Elab_Term_tryLiftAndCoe___closed__3;
lean_object* l_Lean_Elab_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandArrayLit___closed__5;
lean_object* lean_add_decl(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryCoe___closed__3;
lean_object* _init_l_Lean_Elab_Term_State_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_EnvExtension_setState___closed__1;
x_2 = l_Lean_MetavarContext_Inhabited___closed__1;
x_3 = l_Lean_Meta_run___rarg___closed__5;
x_4 = l_Lean_NameGenerator_Inhabited___closed__3;
x_5 = l_Lean_TraceState_Inhabited___closed__1;
x_6 = l_Std_PersistentArray_empty___closed__3;
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
lean_object* _init_l_Lean_Elab_Term_State_inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_State_inhabited___closed__1;
x_3 = l_Std_PersistentArray_empty___closed__3;
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Unhygienic_run___rarg___closed__1;
x_6 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_4);
lean_ctor_set(x_6, 5, x_5);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Term_State_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_State_inhabited___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Exception_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(1);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_Exception_hasToString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Message_toString(x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Exception_hasToString___closed__1;
return x_5;
}
}
else
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_LevelDefEq_10__processPostponedStep___closed__1;
return x_6;
}
}
}
lean_object* l_Lean_Elab_Term_TermElabM_inhabited___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_inhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_TermElabM_inhabited___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_inhabited___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_TermElabM_inhabited(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabResult_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_Inhabited___closed__1;
x_2 = l_Lean_Elab_Term_State_inhabited___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabResult_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_TermElabResult_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Elab_Term_observing(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_3);
x_4 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_11);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_4, 0, x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_4, 0);
lean_dec(x_22);
return x_4;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_dec(x_4);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_4, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_4, 0);
lean_dec(x_27);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_28; 
lean_dec(x_4);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_applyResult(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
}
lean_object* l_Lean_Elab_Term_applyResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_applyResult(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_getEnv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getEnv___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_getEnv___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_getEnv(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_getMCtx___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_getMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getMCtx___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_getMCtx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_getMCtx(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_getLCtx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_getLCtx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_getLCtx(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_getLocalInsts(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_getLocalInsts___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_getLocalInsts(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_getOptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_getOptions___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_getOptions(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_getLevelNames(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 5);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_getLevelNames___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_getLevelNames(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_TermElabM_inhabited___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_getLCtx(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_Expr_fvarId_x21(x_1);
x_9 = lean_local_ctx_find(x_6, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_free_object(x_4);
x_10 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
x_12 = lean_apply_2(x_11, x_2, x_7);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = l_Lean_Expr_fvarId_x21(x_1);
x_17 = lean_local_ctx_find(x_14, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_19 = l_unreachable_x21___rarg(x_18);
x_20 = lean_apply_2(x_19, x_2, x_15);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
}
}
}
lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_getFVarLocalDecl_x21(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_setEnv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_ctor_get(x_5, 2);
x_12 = lean_ctor_get(x_5, 3);
x_13 = lean_ctor_get(x_5, 4);
x_14 = lean_ctor_get(x_5, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_13);
lean_ctor_set(x_15, 5, x_14);
lean_ctor_set(x_3, 0, x_15);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 2);
x_21 = lean_ctor_get(x_3, 3);
x_22 = lean_ctor_get(x_3, 4);
x_23 = lean_ctor_get(x_3, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_18, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_18, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 4);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 5);
lean_inc(x_28);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 x_29 = x_18;
} else {
 lean_dec_ref(x_18);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 6, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_27);
lean_ctor_set(x_30, 5, x_28);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_19);
lean_ctor_set(x_31, 2, x_20);
lean_ctor_set(x_31, 3, x_21);
lean_ctor_set(x_31, 4, x_22);
lean_ctor_set(x_31, 5, x_23);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
lean_object* l_Lean_Elab_Term_setEnv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_setEnv(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_setMCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 1);
lean_dec(x_7);
lean_ctor_set(x_5, 1, x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 2);
x_12 = lean_ctor_get(x_5, 3);
x_13 = lean_ctor_get(x_5, 4);
x_14 = lean_ctor_get(x_5, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_1);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_13);
lean_ctor_set(x_15, 5, x_14);
lean_ctor_set(x_3, 0, x_15);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 2);
x_21 = lean_ctor_get(x_3, 3);
x_22 = lean_ctor_get(x_3, 4);
x_23 = lean_ctor_get(x_3, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_18, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_18, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 4);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 5);
lean_inc(x_28);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 x_29 = x_18;
} else {
 lean_dec_ref(x_18);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 6, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_1);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_27);
lean_ctor_set(x_30, 5, x_28);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_19);
lean_ctor_set(x_31, 2, x_20);
lean_ctor_set(x_31, 3, x_21);
lean_ctor_set(x_31, 4, x_22);
lean_ctor_set(x_31, 5, x_23);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
lean_object* l_Lean_Elab_Term_setMCtx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_setMCtx(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_modifyEnv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_apply_1(x_1, x_7);
lean_ctor_set(x_5, 0, x_8);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
x_16 = lean_ctor_get(x_5, 5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_17 = lean_apply_1(x_1, x_11);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set(x_18, 3, x_14);
lean_ctor_set(x_18, 4, x_15);
lean_ctor_set(x_18, 5, x_16);
lean_ctor_set(x_3, 0, x_18);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_3, 3);
x_25 = lean_ctor_get(x_3, 4);
x_26 = lean_ctor_get(x_3, 5);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_21, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_21, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_21, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_21, 5);
lean_inc(x_32);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 lean_ctor_release(x_21, 4);
 lean_ctor_release(x_21, 5);
 x_33 = x_21;
} else {
 lean_dec_ref(x_21);
 x_33 = lean_box(0);
}
x_34 = lean_apply_1(x_1, x_27);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 6, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_31);
lean_ctor_set(x_35, 5, x_32);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_24);
lean_ctor_set(x_36, 4, x_25);
lean_ctor_set(x_36, 5, x_26);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
lean_object* l_Lean_Elab_Term_modifyEnv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_modifyEnv(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_addContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_4 = l_Lean_Elab_Term_getEnv___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_Term_getMCtx___rarg(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Term_getLCtx(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Term_getOptions(x_2, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_8);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_15);
x_17 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_20, 2, x_11);
lean_ctor_set(x_20, 3, x_18);
x_21 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
}
lean_object* l_Lean_Elab_Term_addContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_addContext(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_ReaderT_read___at_Lean_Elab_Term_monadLog___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_3(x_2, x_6, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_monadLog___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_monadLog___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_monadLog___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 9);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_monadLog___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Std_PersistentArray_push___rarg(x_5, x_1);
lean_ctor_set(x_3, 2, x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
x_14 = lean_ctor_get(x_3, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_15 = l_Std_PersistentArray_push___rarg(x_11, x_1);
x_16 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_13);
lean_ctor_set(x_16, 5, x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
lean_object* _init_l_Lean_Elab_Term_monadLog___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Elab_Term_monadLog___spec__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_monadLog___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_monadLog___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_monadLog___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_monadLog___closed__1;
x_2 = l_Lean_Elab_Term_monadLog___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_monadLog___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_monadLog___lambda__2___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_monadLog___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_monadLog___closed__1;
x_2 = l_Lean_Elab_Term_monadLog___closed__4;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_monadLog___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_monadLog___lambda__3___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_monadLog___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_monadLog___closed__1;
x_2 = l_Lean_Elab_Term_monadLog___closed__6;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_monadLog___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_addContext___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_monadLog___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_monadLog___closed__3;
x_2 = l_Lean_Elab_Term_monadLog___closed__5;
x_3 = l_Lean_Elab_Term_monadLog___closed__7;
x_4 = l_Lean_Elab_Term_monadLog___closed__8;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_monadLog___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_monadLog___lambda__4___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_monadLog___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_monadLog___closed__9;
x_2 = l_Lean_Elab_Term_monadLog___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_monadLog() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_monadLog___closed__11;
return x_1;
}
}
lean_object* l_Lean_Elab_Term_monadLog___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_monadLog___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_monadLog___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_monadLog___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_monadLog___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_monadLog___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_monadLog___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_monadLog___lambda__4(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_withRef___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 9);
x_7 = l_Lean_Elab_replaceRef(x_1, x_6);
lean_dec(x_6);
lean_ctor_set(x_3, 9, x_7);
x_8 = lean_apply_2(x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
x_14 = lean_ctor_get(x_3, 5);
x_15 = lean_ctor_get(x_3, 6);
x_16 = lean_ctor_get(x_3, 7);
x_17 = lean_ctor_get(x_3, 8);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_21 = lean_ctor_get(x_3, 9);
lean_inc(x_21);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_22 = l_Lean_Elab_replaceRef(x_1, x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_10);
lean_ctor_set(x_23, 2, x_11);
lean_ctor_set(x_23, 3, x_12);
lean_ctor_set(x_23, 4, x_13);
lean_ctor_set(x_23, 5, x_14);
lean_ctor_set(x_23, 6, x_15);
lean_ctor_set(x_23, 7, x_16);
lean_ctor_set(x_23, 8, x_17);
lean_ctor_set(x_23, 9, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*10, x_18);
lean_ctor_set_uint8(x_23, sizeof(void*)*10 + 1, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*10 + 2, x_20);
x_24 = lean_apply_2(x_2, x_23, x_4);
return x_24;
}
}
}
lean_object* l_Lean_Elab_Term_withRef(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withRef___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_withRef___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_withRef___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_throwError___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 9);
x_4 = l_Lean_Syntax_getPos(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
}
}
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Term_throwError___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 2);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_FileMap_toPosition(x_6, x_3);
x_9 = l_Lean_Elab_Term_addContext(x_1, x_4, x_5);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(0);
x_13 = l_String_splitAux___main___closed__1;
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_2);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_box(0);
x_18 = l_String_splitAux___main___closed__1;
lean_inc(x_7);
x_19 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_8);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_18);
lean_ctor_set(x_19, 4, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*5, x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
}
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Term_throwError___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Elab_getRefPos___at_Lean_Elab_Term_throwError___spec__2(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Term_throwError___spec__3(x_1, x_2, x_6, x_3, x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 7);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_7 = lean_ctor_get(x_2, 9);
lean_inc(x_5);
x_8 = l_Lean_Elab_getBetterRef(x_7, x_5);
x_9 = l_Lean_Elab_replaceRef(x_8, x_7);
lean_dec(x_7);
lean_dec(x_8);
lean_inc(x_5);
lean_ctor_set(x_2, 9, x_9);
if (x_6 == 0)
{
uint8_t x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_5);
x_10 = 2;
x_11 = l_Lean_Elab_mkMessage___at_Lean_Elab_Term_throwError___spec__1(x_1, x_10, x_2, x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; 
x_21 = l_Lean_Elab_addMacroStack(x_1, x_5);
x_22 = 2;
x_23 = l_Lean_Elab_mkMessage___at_Lean_Elab_Term_throwError___spec__1(x_21, x_22, x_2, x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
x_35 = lean_ctor_get(x_2, 2);
x_36 = lean_ctor_get(x_2, 3);
x_37 = lean_ctor_get(x_2, 4);
x_38 = lean_ctor_get(x_2, 5);
x_39 = lean_ctor_get(x_2, 6);
x_40 = lean_ctor_get(x_2, 7);
x_41 = lean_ctor_get(x_2, 8);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_43 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_44 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_45 = lean_ctor_get(x_2, 9);
lean_inc(x_45);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_2);
lean_inc(x_40);
x_46 = l_Lean_Elab_getBetterRef(x_45, x_40);
x_47 = l_Lean_Elab_replaceRef(x_46, x_45);
lean_dec(x_45);
lean_dec(x_46);
lean_inc(x_40);
x_48 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_48, 0, x_33);
lean_ctor_set(x_48, 1, x_34);
lean_ctor_set(x_48, 2, x_35);
lean_ctor_set(x_48, 3, x_36);
lean_ctor_set(x_48, 4, x_37);
lean_ctor_set(x_48, 5, x_38);
lean_ctor_set(x_48, 6, x_39);
lean_ctor_set(x_48, 7, x_40);
lean_ctor_set(x_48, 8, x_41);
lean_ctor_set(x_48, 9, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*10, x_42);
lean_ctor_set_uint8(x_48, sizeof(void*)*10 + 1, x_43);
lean_ctor_set_uint8(x_48, sizeof(void*)*10 + 2, x_44);
if (x_44 == 0)
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_40);
x_49 = 2;
x_50 = l_Lean_Elab_mkMessage___at_Lean_Elab_Term_throwError___spec__1(x_1, x_49, x_48, x_3);
lean_dec(x_48);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_51);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_53;
 lean_ctor_set_tag(x_56, 1);
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
return x_56;
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_57 = l_Lean_Elab_addMacroStack(x_1, x_40);
x_58 = 2;
x_59 = l_Lean_Elab_mkMessage___at_Lean_Elab_Term_throwError___spec__1(x_57, x_58, x_48, x_3);
lean_dec(x_48);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_60);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_62;
 lean_ctor_set_tag(x_65, 1);
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_61);
return x_65;
}
}
}
}
lean_object* l_Lean_Elab_Term_throwError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwError___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_throwError___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_getRefPos___at_Lean_Elab_Term_throwError___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Term_throwError___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Term_throwError___spec__3(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Term_throwError___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Elab_mkMessage___at_Lean_Elab_Term_throwError___spec__1(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_throwErrorAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 9);
x_7 = l_Lean_Elab_replaceRef(x_1, x_6);
lean_dec(x_6);
lean_ctor_set(x_3, 9, x_7);
x_8 = l_Lean_Elab_Term_throwError___rarg(x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
x_14 = lean_ctor_get(x_3, 5);
x_15 = lean_ctor_get(x_3, 6);
x_16 = lean_ctor_get(x_3, 7);
x_17 = lean_ctor_get(x_3, 8);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_21 = lean_ctor_get(x_3, 9);
lean_inc(x_21);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_22 = l_Lean_Elab_replaceRef(x_1, x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_10);
lean_ctor_set(x_23, 2, x_11);
lean_ctor_set(x_23, 3, x_12);
lean_ctor_set(x_23, 4, x_13);
lean_ctor_set(x_23, 5, x_14);
lean_ctor_set(x_23, 6, x_15);
lean_ctor_set(x_23, 7, x_16);
lean_ctor_set(x_23, 8, x_17);
lean_ctor_set(x_23, 9, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*10, x_18);
lean_ctor_set_uint8(x_23, sizeof(void*)*10 + 1, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*10 + 2, x_20);
x_24 = l_Lean_Elab_Term_throwError___rarg(x_2, x_23, x_4);
return x_24;
}
}
}
lean_object* l_Lean_Elab_Term_throwErrorAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwErrorAt___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_throwErrorAt___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_throwUnsupportedSyntax___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwUnsupportedSyntax___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_throwUnsupportedSyntax(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_withIncRecDepth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 5);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 6);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 7);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 8);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_16 = lean_ctor_get(x_2, 9);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 4);
lean_inc(x_18);
x_19 = lean_nat_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_2);
x_20 = x_3;
goto block_36;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_37 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_38 = l_Lean_Elab_Term_throwError___rarg(x_37, x_2, x_3);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
block_36:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_4, 4);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 3);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_17, x_24);
lean_dec(x_17);
lean_ctor_set(x_4, 3, x_25);
x_26 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_5);
lean_ctor_set(x_26, 2, x_6);
lean_ctor_set(x_26, 3, x_7);
lean_ctor_set(x_26, 4, x_8);
lean_ctor_set(x_26, 5, x_9);
lean_ctor_set(x_26, 6, x_10);
lean_ctor_set(x_26, 7, x_11);
lean_ctor_set(x_26, 8, x_12);
lean_ctor_set(x_26, 9, x_16);
lean_ctor_set_uint8(x_26, sizeof(void*)*10, x_13);
lean_ctor_set_uint8(x_26, sizeof(void*)*10 + 1, x_14);
lean_ctor_set_uint8(x_26, sizeof(void*)*10 + 2, x_15);
x_27 = lean_apply_2(x_1, x_26, x_20);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_ctor_get(x_4, 1);
x_30 = lean_ctor_get(x_4, 2);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_4);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_17, x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_32);
lean_ctor_set(x_33, 4, x_18);
x_34 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_5);
lean_ctor_set(x_34, 2, x_6);
lean_ctor_set(x_34, 3, x_7);
lean_ctor_set(x_34, 4, x_8);
lean_ctor_set(x_34, 5, x_9);
lean_ctor_set(x_34, 6, x_10);
lean_ctor_set(x_34, 7, x_11);
lean_ctor_set(x_34, 8, x_12);
lean_ctor_set(x_34, 9, x_16);
lean_ctor_set_uint8(x_34, sizeof(void*)*10, x_13);
lean_ctor_set_uint8(x_34, sizeof(void*)*10 + 1, x_14);
lean_ctor_set_uint8(x_34, sizeof(void*)*10 + 2, x_15);
x_35 = lean_apply_2(x_1, x_34, x_20);
return x_35;
}
}
}
}
lean_object* l_Lean_Elab_Term_withIncRecDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withIncRecDepth___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 8);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_getCurrMacroScope___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_getCurrMacroScope(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_Term_getEnv___rarg(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_environment_main_module(x_4);
lean_ctor_set(x_2, 0, x_5);
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
x_8 = lean_environment_main_module(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
lean_object* l_Lean_Elab_Term_getMainModule(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getMainModule___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_getMainModule___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_getMainModule(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_withFreshMacroScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 5);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_ctor_set(x_3, 5, x_7);
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 8);
lean_dec(x_9);
lean_ctor_set(x_2, 8, x_5);
x_10 = lean_apply_2(x_1, x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get(x_2, 3);
x_15 = lean_ctor_get(x_2, 4);
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_ctor_get(x_2, 6);
x_18 = lean_ctor_get(x_2, 7);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_22 = lean_ctor_get(x_2, 9);
lean_inc(x_22);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_12);
lean_ctor_set(x_23, 2, x_13);
lean_ctor_set(x_23, 3, x_14);
lean_ctor_set(x_23, 4, x_15);
lean_ctor_set(x_23, 5, x_16);
lean_ctor_set(x_23, 6, x_17);
lean_ctor_set(x_23, 7, x_18);
lean_ctor_set(x_23, 8, x_5);
lean_ctor_set(x_23, 9, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*10, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*10 + 1, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*10 + 2, x_21);
x_24 = lean_apply_2(x_1, x_23, x_3);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
x_27 = lean_ctor_get(x_3, 2);
x_28 = lean_ctor_get(x_3, 3);
x_29 = lean_ctor_get(x_3, 4);
x_30 = lean_ctor_get(x_3, 5);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_30, x_31);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 2, x_27);
lean_ctor_set(x_33, 3, x_28);
lean_ctor_set(x_33, 4, x_29);
lean_ctor_set(x_33, 5, x_32);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 4);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 5);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 6);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 7);
lean_inc(x_41);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_43 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_44 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_45 = lean_ctor_get(x_2, 9);
lean_inc(x_45);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 lean_ctor_release(x_2, 8);
 lean_ctor_release(x_2, 9);
 x_46 = x_2;
} else {
 lean_dec_ref(x_2);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 10, 3);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_35);
lean_ctor_set(x_47, 2, x_36);
lean_ctor_set(x_47, 3, x_37);
lean_ctor_set(x_47, 4, x_38);
lean_ctor_set(x_47, 5, x_39);
lean_ctor_set(x_47, 6, x_40);
lean_ctor_set(x_47, 7, x_41);
lean_ctor_set(x_47, 8, x_30);
lean_ctor_set(x_47, 9, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*10, x_42);
lean_ctor_set_uint8(x_47, sizeof(void*)*10 + 1, x_43);
lean_ctor_set_uint8(x_47, sizeof(void*)*10 + 2, x_44);
x_48 = lean_apply_2(x_1, x_47, x_33);
return x_48;
}
}
}
lean_object* l_Lean_Elab_Term_withFreshMacroScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withFreshMacroScope___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_monadQuotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getCurrMacroScope___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_monadQuotation___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getMainModule___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_monadQuotation___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withFreshMacroScope), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_monadQuotation___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_monadQuotation___closed__1;
x_2 = l_Lean_Elab_Term_monadQuotation___closed__2;
x_3 = l_Lean_Elab_Term_monadQuotation___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_monadQuotation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_monadQuotation___closed__4;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_mkMacroAttribute___closed__2;
x_2 = l_Lean_mkAppStx___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("termElabAttribute");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_mkTermElabAttribute___closed__1;
x_2 = l_Lean_Elab_Term_mkTermElabAttribute___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinTermElab");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_mkTermElabAttribute___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("termElab");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_mkTermElabAttribute___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TermElab");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_mkTermElabAttribute___closed__1;
x_2 = l_Lean_Elab_Term_mkTermElabAttribute___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_mkTermElabAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_Elab_Term_mkTermElabAttribute___closed__3;
x_3 = l_Lean_Elab_Term_mkTermElabAttribute___closed__5;
x_4 = l_Lean_Elab_Term_mkTermElabAttribute___closed__7;
x_5 = l_Lean_mkAppStx___closed__6;
x_6 = l_Lean_Elab_Term_mkTermElabAttribute___closed__9;
x_7 = l_Lean_Parser_termParser___closed__1;
x_8 = l_Lean_Elab_mkElabAttribute___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_1);
return x_8;
}
}
lean_object* l_Std_mkHashMap___at_Lean_Elab_Term_termElabAttribute___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__1___closed__1;
x_3 = l_Std_PersistentHashMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__1___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_termElabAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_termElabAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_termElabAttribute___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_termElabAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_Elab_Term_termElabAttribute___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_termElabAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Term_termElabAttribute___closed__3;
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
lean_object* _init_l_Lean_Elab_Term_termElabAttribute___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_termElabAttribute___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_LVal_hasToString(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
return x_4;
}
default: 
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = 0;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_formatStxAux___main(x_6, x_7, x_8, x_5);
x_10 = l_Lean_Options_empty;
x_11 = l_Lean_Format_pretty(x_9, x_10);
x_12 = l_List_repr___rarg___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_List_repr___rarg___closed__3;
x_15 = lean_string_append(x_13, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_Elab_Term_getDeclName_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_getDeclName_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_getDeclName_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_getCurrNamespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_getCurrNamespace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_getCurrNamespace(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_getOpenDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 6);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_getOpenDecls___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_getOpenDecls(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_getTraceState___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_getTraceState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getTraceState___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_getTraceState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_getTraceState(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_setTraceState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 4);
lean_dec(x_7);
lean_ctor_set(x_5, 4, x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_5, 2);
x_13 = lean_ctor_get(x_5, 3);
x_14 = lean_ctor_get(x_5, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_13);
lean_ctor_set(x_15, 4, x_1);
lean_ctor_set(x_15, 5, x_14);
lean_ctor_set(x_3, 0, x_15);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 2);
x_21 = lean_ctor_get(x_3, 3);
x_22 = lean_ctor_get(x_3, 4);
x_23 = lean_ctor_get(x_3, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_18, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 5);
lean_inc(x_28);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 x_29 = x_18;
} else {
 lean_dec_ref(x_18);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 6, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_26);
lean_ctor_set(x_30, 3, x_27);
lean_ctor_set(x_30, 4, x_1);
lean_ctor_set(x_30, 5, x_28);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_19);
lean_ctor_set(x_31, 2, x_20);
lean_ctor_set(x_31, 3, x_21);
lean_ctor_set(x_31, 4, x_22);
lean_ctor_set(x_31, 5, x_23);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
lean_object* l_Lean_Elab_Term_setTraceState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_setTraceState(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_isExprMVarAssigned(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_getMCtx___rarg(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_metavar_ctx_is_expr_assigned(x_6, x_1);
x_8 = lean_box(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_metavar_ctx_is_expr_assigned(x_9, x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
lean_object* l_Lean_Elab_Term_isExprMVarAssigned___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_isExprMVarAssigned(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_getMCtx___rarg(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_MetavarContext_getDecl(x_6, x_1);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = l_Lean_MetavarContext_getDecl(x_8, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Elab_Term_getMVarDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_getMVarDecl(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_assignExprMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = l_Lean_MetavarContext_assignExpr(x_8, x_1, x_2);
lean_ctor_set(x_6, 1, x_9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_6, 2);
x_15 = lean_ctor_get(x_6, 3);
x_16 = lean_ctor_get(x_6, 4);
x_17 = lean_ctor_get(x_6, 5);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_18 = l_Lean_MetavarContext_assignExpr(x_13, x_1, x_2);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_16);
lean_ctor_set(x_19, 5, x_17);
lean_ctor_set(x_4, 0, x_19);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_ctor_get(x_4, 2);
x_25 = lean_ctor_get(x_4, 3);
x_26 = lean_ctor_get(x_4, 4);
x_27 = lean_ctor_get(x_4, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_22, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_22, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_22, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_22, 5);
lean_inc(x_33);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 lean_ctor_release(x_22, 4);
 lean_ctor_release(x_22, 5);
 x_34 = x_22;
} else {
 lean_dec_ref(x_22);
 x_34 = lean_box(0);
}
x_35 = l_Lean_MetavarContext_assignExpr(x_29, x_1, x_2);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 6, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_32);
lean_ctor_set(x_36, 5, x_33);
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_23);
lean_ctor_set(x_37, 2, x_24);
lean_ctor_set(x_37, 3, x_25);
lean_ctor_set(x_37, 4, x_26);
lean_ctor_set(x_37, 5, x_27);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
lean_object* l_Lean_Elab_Term_assignExprMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_assignExprMVar(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_assignLevelMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_metavar_ctx_assign_level(x_8, x_1, x_2);
lean_ctor_set(x_6, 1, x_9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_6, 2);
x_15 = lean_ctor_get(x_6, 3);
x_16 = lean_ctor_get(x_6, 4);
x_17 = lean_ctor_get(x_6, 5);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_18 = lean_metavar_ctx_assign_level(x_13, x_1, x_2);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_16);
lean_ctor_set(x_19, 5, x_17);
lean_ctor_set(x_4, 0, x_19);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_ctor_get(x_4, 2);
x_25 = lean_ctor_get(x_4, 3);
x_26 = lean_ctor_get(x_4, 4);
x_27 = lean_ctor_get(x_4, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_22, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_22, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_22, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_22, 5);
lean_inc(x_33);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 lean_ctor_release(x_22, 4);
 lean_ctor_release(x_22, 5);
 x_34 = x_22;
} else {
 lean_dec_ref(x_22);
 x_34 = lean_box(0);
}
x_35 = lean_metavar_ctx_assign_level(x_29, x_1, x_2);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 6, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_32);
lean_ctor_set(x_36, 5, x_33);
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_23);
lean_ctor_set(x_37, 2, x_24);
lean_ctor_set(x_37, 3, x_25);
lean_ctor_set(x_37, 4, x_26);
lean_ctor_set(x_37, 5, x_27);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
lean_object* l_Lean_Elab_Term_assignLevelMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_assignLevelMVar(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_logTrace___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Term_throwError___spec__3(x_3, x_2, x_1, x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_8, 2);
x_12 = l_Std_PersistentArray_push___rarg(x_11, x_10);
lean_ctor_set(x_8, 2, x_12);
x_13 = lean_box(0);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_21 = l_Std_PersistentArray_push___rarg(x_17, x_14);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set(x_22, 3, x_18);
lean_ctor_set(x_22, 4, x_19);
lean_ctor_set(x_22, 5, x_20);
x_23 = lean_box(0);
lean_ctor_set(x_6, 1, x_22);
lean_ctor_set(x_6, 0, x_23);
return x_6;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_6, 1);
x_25 = lean_ctor_get(x_6, 0);
lean_inc(x_24);
lean_inc(x_25);
lean_dec(x_6);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 4);
lean_inc(x_30);
x_31 = lean_ctor_get(x_24, 5);
lean_inc(x_31);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 lean_ctor_release(x_24, 4);
 lean_ctor_release(x_24, 5);
 x_32 = x_24;
} else {
 lean_dec_ref(x_24);
 x_32 = lean_box(0);
}
x_33 = l_Std_PersistentArray_push___rarg(x_28, x_25);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 6, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 4, x_30);
lean_ctor_set(x_34, 5, x_31);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Elab_getRefPos___at_Lean_Elab_Term_throwError___spec__2(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_logAt___at_Lean_Elab_Term_logTrace___spec__2(x_6, x_1, x_2, x_3, x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_logTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_8, 1);
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_11);
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
x_14 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = 0;
x_16 = l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(x_15, x_14, x_3, x_4);
return x_16;
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_logTrace___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_logAt___at_Lean_Elab_Term_logTrace___spec__2(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_logTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_logTrace(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_trace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Term_getOptions(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_1);
x_9 = l_Lean_checkTraceOption(x_7, x_1);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_free_object(x_5);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_2, x_11);
x_13 = l_Lean_Elab_Term_logTrace(x_1, x_12, x_3, x_8);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
lean_inc(x_1);
x_16 = l_Lean_checkTraceOption(x_14, x_1);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_box(0);
x_20 = lean_apply_1(x_2, x_19);
x_21 = l_Lean_Elab_Term_logTrace(x_1, x_20, x_3, x_15);
return x_21;
}
}
}
}
lean_object* l_Lean_Elab_Term_trace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_trace(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_logDbgTrace___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l___private_Lean_Meta_Basic_12__regTraceClasses___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_logDbgTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_getOptions(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_Elab_Term_logDbgTrace___closed__1;
x_9 = l_Lean_checkTraceOption(x_6, x_8);
lean_dec(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_box(0);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; 
lean_free_object(x_4);
x_11 = l_Lean_Elab_Term_logTrace(x_8, x_1, x_2, x_7);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = l_Lean_Elab_Term_logDbgTrace___closed__1;
x_15 = l_Lean_checkTraceOption(x_12, x_14);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_Elab_Term_logTrace(x_14, x_1, x_2, x_13);
return x_18;
}
}
}
}
lean_object* l_Lean_Elab_Term_logDbgTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_logDbgTrace(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_throwErrorIfErrors___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Error(s)");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_throwErrorIfErrors___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_throwErrorIfErrors___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_throwErrorIfErrors___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_throwErrorIfErrors___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_throwErrorIfErrors(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
x_4 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Elab_Term_throwErrorIfErrors___closed__3;
x_8 = l_Lean_Elab_Term_throwError___rarg(x_7, x_1, x_2);
return x_8;
}
}
}
lean_object* l_Lean_Elab_Term_traceAtCmdPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 9);
x_7 = lean_box(0);
x_8 = l_Lean_Elab_replaceRef(x_7, x_6);
lean_dec(x_6);
lean_ctor_set(x_3, 9, x_8);
x_9 = l_Lean_Elab_Term_getOptions(x_3, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_1);
x_13 = l_Lean_checkTraceOption(x_11, x_1);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_free_object(x_9);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_2, x_15);
x_17 = l_Lean_Elab_Term_logTrace(x_1, x_16, x_3, x_12);
lean_dec(x_3);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
lean_inc(x_1);
x_20 = l_Lean_checkTraceOption(x_18, x_1);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_box(0);
x_24 = lean_apply_1(x_2, x_23);
x_25 = l_Lean_Elab_Term_logTrace(x_1, x_24, x_3, x_19);
lean_dec(x_3);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_3, 1);
x_28 = lean_ctor_get(x_3, 2);
x_29 = lean_ctor_get(x_3, 3);
x_30 = lean_ctor_get(x_3, 4);
x_31 = lean_ctor_get(x_3, 5);
x_32 = lean_ctor_get(x_3, 6);
x_33 = lean_ctor_get(x_3, 7);
x_34 = lean_ctor_get(x_3, 8);
x_35 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_36 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_38 = lean_ctor_get(x_3, 9);
lean_inc(x_38);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_3);
x_39 = lean_box(0);
x_40 = l_Lean_Elab_replaceRef(x_39, x_38);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_41, 0, x_26);
lean_ctor_set(x_41, 1, x_27);
lean_ctor_set(x_41, 2, x_28);
lean_ctor_set(x_41, 3, x_29);
lean_ctor_set(x_41, 4, x_30);
lean_ctor_set(x_41, 5, x_31);
lean_ctor_set(x_41, 6, x_32);
lean_ctor_set(x_41, 7, x_33);
lean_ctor_set(x_41, 8, x_34);
lean_ctor_set(x_41, 9, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*10, x_35);
lean_ctor_set_uint8(x_41, sizeof(void*)*10 + 1, x_36);
lean_ctor_set_uint8(x_41, sizeof(void*)*10 + 2, x_37);
x_42 = l_Lean_Elab_Term_getOptions(x_41, x_4);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
lean_inc(x_1);
x_46 = l_Lean_checkTraceOption(x_43, x_1);
lean_dec(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_41);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_box(0);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_45);
x_49 = lean_box(0);
x_50 = lean_apply_1(x_2, x_49);
x_51 = l_Lean_Elab_Term_logTrace(x_1, x_50, x_41, x_44);
lean_dec(x_41);
return x_51;
}
}
}
}
lean_object* l_Lean_Elab_Term_dbgTrace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_apply_1(x_1, x_2);
x_6 = l_Lean_Meta_dbgTrace___rarg___closed__1;
x_7 = lean_dbg_trace(x_5, x_6);
x_8 = lean_apply_2(x_7, x_3, x_4);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_dbgTrace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_dbgTrace___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Term_1__mkMessageAux(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 9);
lean_inc(x_4);
x_5 = l_Lean_Syntax_getPos(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Elab_mkMessageCore(x_6, x_7, x_2, x_3, x_8);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = l_Lean_Elab_mkMessageCore(x_10, x_11, x_2, x_3, x_12);
lean_dec(x_11);
return x_13;
}
}
}
lean_object* l___private_Lean_Elab_Term_1__mkMessageAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l___private_Lean_Elab_Term_1__mkMessageAux(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Term_2__fromMetaException(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Meta_Exception_toMessageData(x_2);
x_4 = 2;
x_5 = l___private_Lean_Elab_Term_1__mkMessageAux(x_1, x_3, x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = l_Std_PersistentArray_foldlMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__2(x_1, x_8, x_5);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = 0;
lean_inc(x_1);
x_10 = l___private_Lean_Elab_Term_1__mkMessageAux(x_1, x_8, x_9);
x_11 = l_Std_PersistentArray_push___rarg(x_5, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_4 = x_13;
x_5 = x_11;
goto _start;
}
}
}
lean_object* l_Std_PersistentArray_foldlMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__3(x_1, x_4, x_4, x_5, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__4(x_1, x_7, x_7, x_8, x_3);
return x_9;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = 0;
lean_inc(x_1);
x_10 = l___private_Lean_Elab_Term_1__mkMessageAux(x_1, x_8, x_9);
x_11 = l_Std_PersistentArray_push___rarg(x_5, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_4 = x_13;
x_5 = x_11;
goto _start;
}
}
}
lean_object* l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Term_3__fromMetaState___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_5 = l_Std_PersistentArray_foldlMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__2(x_1, x_4, x_3);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__5(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Term_3__fromMetaState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 0);
lean_dec(x_10);
x_11 = l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Term_3__fromMetaState___spec__1(x_1, x_7, x_9);
lean_dec(x_7);
lean_ctor_set(x_3, 4, x_4);
lean_ctor_set(x_2, 2, x_11);
lean_ctor_set(x_2, 0, x_3);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get(x_2, 3);
x_15 = lean_ctor_get(x_2, 4);
x_16 = lean_ctor_get(x_2, 5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_17 = l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Term_3__fromMetaState___spec__1(x_1, x_7, x_13);
lean_dec(x_7);
lean_ctor_set(x_3, 4, x_4);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_14);
lean_ctor_set(x_18, 4, x_15);
lean_ctor_set(x_18, 5, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get(x_3, 2);
x_22 = lean_ctor_get(x_3, 3);
x_23 = lean_ctor_get(x_3, 4);
x_24 = lean_ctor_get(x_3, 5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 4);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 5);
lean_inc(x_30);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_31 = x_2;
} else {
 lean_dec_ref(x_2);
 x_31 = lean_box(0);
}
x_32 = l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Term_3__fromMetaState___spec__1(x_1, x_25, x_27);
lean_dec(x_25);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_20);
lean_ctor_set(x_33, 2, x_21);
lean_ctor_set(x_33, 3, x_22);
lean_ctor_set(x_33, 4, x_4);
lean_ctor_set(x_33, 5, x_24);
if (lean_is_scalar(x_31)) {
 x_34 = lean_alloc_ctor(0, 6, 0);
} else {
 x_34 = x_31;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_28);
lean_ctor_set(x_34, 4, x_29);
lean_ctor_set(x_34, 5, x_30);
return x_34;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Std_PersistentArray_foldlMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentArray_foldlMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Lean_Elab_Term_3__fromMetaState___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Term_3__fromMetaState___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Term_3__fromMetaState___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_liftMetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_8);
x_9 = lean_apply_2(x_1, x_7, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_11, x_6);
lean_ctor_set(x_9, 1, x_12);
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
x_15 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_14, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_18);
x_21 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_19, x_6);
lean_ctor_set(x_9, 1, x_21);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
lean_inc(x_2);
x_24 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_22);
x_25 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_23, x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
x_29 = lean_ctor_get(x_4, 2);
x_30 = lean_ctor_get(x_4, 3);
x_31 = lean_ctor_get(x_4, 4);
x_32 = lean_ctor_get(x_4, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = l_Lean_TraceState_Inhabited___closed__1;
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_32);
x_36 = lean_apply_2(x_1, x_33, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_38, x_31);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
lean_inc(x_2);
x_45 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_42);
x_46 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_43, x_31);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Elab_Term_liftMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_liftMetaM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_ppGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_8);
x_9 = l_Lean_Meta_ppGoal(x_1, x_7, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_11, x_6);
lean_ctor_set(x_9, 1, x_12);
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
x_15 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_14, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_ctor_get(x_4, 3);
x_21 = lean_ctor_get(x_4, 4);
x_22 = lean_ctor_get(x_4, 5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = l_Lean_TraceState_Inhabited___closed__1;
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_19);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set(x_25, 5, x_22);
x_26 = l_Lean_Meta_ppGoal(x_1, x_23, x_25);
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
x_30 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_28, x_21);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
lean_object* l_Lean_Elab_Term_isType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_8);
x_9 = l_Lean_Meta_isType(x_1, x_7, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_11, x_6);
lean_ctor_set(x_9, 1, x_12);
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
x_15 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_14, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_18);
x_21 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_19, x_6);
lean_ctor_set(x_9, 1, x_21);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
lean_inc(x_2);
x_24 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_22);
x_25 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_23, x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
x_29 = lean_ctor_get(x_4, 2);
x_30 = lean_ctor_get(x_4, 3);
x_31 = lean_ctor_get(x_4, 4);
x_32 = lean_ctor_get(x_4, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = l_Lean_TraceState_Inhabited___closed__1;
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_32);
x_36 = l_Lean_Meta_isType(x_1, x_33, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_38, x_31);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
lean_inc(x_2);
x_45 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_42);
x_46 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_43, x_31);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Elab_Term_isTypeFormer(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_8);
x_9 = l_Lean_Meta_isTypeFormer(x_1, x_7, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_11, x_6);
lean_ctor_set(x_9, 1, x_12);
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
x_15 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_14, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_18);
x_21 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_19, x_6);
lean_ctor_set(x_9, 1, x_21);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
lean_inc(x_2);
x_24 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_22);
x_25 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_23, x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
x_29 = lean_ctor_get(x_4, 2);
x_30 = lean_ctor_get(x_4, 3);
x_31 = lean_ctor_get(x_4, 4);
x_32 = lean_ctor_get(x_4, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = l_Lean_TraceState_Inhabited___closed__1;
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_32);
x_36 = l_Lean_Meta_isTypeFormer(x_1, x_33, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_38, x_31);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
lean_inc(x_2);
x_45 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_42);
x_46 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_43, x_31);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Elab_Term_isTypeFormerType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_8);
x_9 = l_Lean_Meta_isTypeFormerType___main(x_1, x_7, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_11, x_6);
lean_ctor_set(x_9, 1, x_12);
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
x_15 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_14, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_18);
x_21 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_19, x_6);
lean_ctor_set(x_9, 1, x_21);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
lean_inc(x_2);
x_24 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_22);
x_25 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_23, x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
x_29 = lean_ctor_get(x_4, 2);
x_30 = lean_ctor_get(x_4, 3);
x_31 = lean_ctor_get(x_4, 4);
x_32 = lean_ctor_get(x_4, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = l_Lean_TraceState_Inhabited___closed__1;
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_32);
x_36 = l_Lean_Meta_isTypeFormerType___main(x_1, x_33, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_38, x_31);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
lean_inc(x_2);
x_45 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_42);
x_46 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_43, x_31);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Elab_Term_isDefEqNoConstantApprox(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; 
x_13 = 1;
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_13);
lean_ctor_set_uint8(x_11, sizeof(void*)*1 + 1, x_13);
lean_ctor_set_uint8(x_11, sizeof(void*)*1 + 2, x_13);
x_14 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_8, x_5);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_16, x_7);
lean_ctor_set(x_14, 1, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_19, x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_3);
x_25 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_23);
x_26 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_24, x_7);
lean_ctor_set(x_14, 1, x_26);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
lean_inc(x_3);
x_29 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_27);
x_30 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_28, x_7);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_11, 0);
x_33 = lean_ctor_get_uint8(x_11, sizeof(void*)*1 + 3);
x_34 = lean_ctor_get_uint8(x_11, sizeof(void*)*1 + 4);
x_35 = lean_ctor_get_uint8(x_11, sizeof(void*)*1 + 5);
x_36 = lean_ctor_get_uint8(x_11, sizeof(void*)*1 + 6);
lean_inc(x_32);
lean_dec(x_11);
x_37 = 1;
x_38 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 1, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 2, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 3, x_33);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 4, x_34);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 5, x_35);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 6, x_36);
lean_ctor_set(x_8, 0, x_38);
x_39 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_8, x_5);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_41, x_7);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_39, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_47 = x_39;
} else {
 lean_dec_ref(x_39);
 x_47 = lean_box(0);
}
lean_inc(x_3);
x_48 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_45);
x_49 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_46, x_7);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_51 = lean_ctor_get(x_8, 0);
x_52 = lean_ctor_get(x_8, 1);
x_53 = lean_ctor_get(x_8, 2);
x_54 = lean_ctor_get(x_8, 3);
x_55 = lean_ctor_get(x_8, 4);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_8);
x_56 = lean_ctor_get(x_51, 0);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_51, sizeof(void*)*1 + 3);
x_58 = lean_ctor_get_uint8(x_51, sizeof(void*)*1 + 4);
x_59 = lean_ctor_get_uint8(x_51, sizeof(void*)*1 + 5);
x_60 = lean_ctor_get_uint8(x_51, sizeof(void*)*1 + 6);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_61 = x_51;
} else {
 lean_dec_ref(x_51);
 x_61 = lean_box(0);
}
x_62 = 1;
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 1, 7);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1 + 1, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1 + 2, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1 + 3, x_57);
lean_ctor_set_uint8(x_63, sizeof(void*)*1 + 4, x_58);
lean_ctor_set_uint8(x_63, sizeof(void*)*1 + 5, x_59);
lean_ctor_set_uint8(x_63, sizeof(void*)*1 + 6, x_60);
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_52);
lean_ctor_set(x_64, 2, x_53);
lean_ctor_set(x_64, 3, x_54);
lean_ctor_set(x_64, 4, x_55);
x_65 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_64, x_5);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
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
x_69 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_67, x_7);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
 x_73 = lean_box(0);
}
lean_inc(x_3);
x_74 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_71);
x_75 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_72, x_7);
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_73;
}
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_77 = lean_ctor_get(x_5, 0);
x_78 = lean_ctor_get(x_5, 1);
x_79 = lean_ctor_get(x_5, 2);
x_80 = lean_ctor_get(x_5, 3);
x_81 = lean_ctor_get(x_5, 4);
x_82 = lean_ctor_get(x_5, 5);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_5);
x_83 = lean_ctor_get(x_3, 0);
lean_inc(x_83);
x_84 = l_Lean_TraceState_Inhabited___closed__1;
x_85 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_85, 0, x_77);
lean_ctor_set(x_85, 1, x_78);
lean_ctor_set(x_85, 2, x_79);
lean_ctor_set(x_85, 3, x_80);
lean_ctor_set(x_85, 4, x_84);
lean_ctor_set(x_85, 5, x_82);
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_83, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 3);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 4);
lean_inc(x_90);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 lean_ctor_release(x_83, 2);
 lean_ctor_release(x_83, 3);
 lean_ctor_release(x_83, 4);
 x_91 = x_83;
} else {
 lean_dec_ref(x_83);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_86, 0);
lean_inc(x_92);
x_93 = lean_ctor_get_uint8(x_86, sizeof(void*)*1 + 3);
x_94 = lean_ctor_get_uint8(x_86, sizeof(void*)*1 + 4);
x_95 = lean_ctor_get_uint8(x_86, sizeof(void*)*1 + 5);
x_96 = lean_ctor_get_uint8(x_86, sizeof(void*)*1 + 6);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_97 = x_86;
} else {
 lean_dec_ref(x_86);
 x_97 = lean_box(0);
}
x_98 = 1;
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 1, 7);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_92);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 1, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 2, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 3, x_93);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 4, x_94);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 5, x_95);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 6, x_96);
if (lean_is_scalar(x_91)) {
 x_100 = lean_alloc_ctor(0, 5, 0);
} else {
 x_100 = x_91;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_87);
lean_ctor_set(x_100, 2, x_88);
lean_ctor_set(x_100, 3, x_89);
lean_ctor_set(x_100, 4, x_90);
x_101 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_100, x_85);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_103, x_81);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_102);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_101, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_101, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_109 = x_101;
} else {
 lean_dec_ref(x_101);
 x_109 = lean_box(0);
}
lean_inc(x_3);
x_110 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_107);
x_111 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_108, x_81);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
lean_object* l_Lean_Elab_Term_isDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; 
x_13 = 1;
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_13);
lean_ctor_set_uint8(x_11, sizeof(void*)*1 + 1, x_13);
lean_ctor_set_uint8(x_11, sizeof(void*)*1 + 2, x_13);
lean_ctor_set_uint8(x_11, sizeof(void*)*1 + 3, x_13);
x_14 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_8, x_5);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_16, x_7);
lean_ctor_set(x_14, 1, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_19, x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_3);
x_25 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_23);
x_26 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_24, x_7);
lean_ctor_set(x_14, 1, x_26);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
lean_inc(x_3);
x_29 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_27);
x_30 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_28, x_7);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_11, 0);
x_33 = lean_ctor_get_uint8(x_11, sizeof(void*)*1 + 4);
x_34 = lean_ctor_get_uint8(x_11, sizeof(void*)*1 + 5);
x_35 = lean_ctor_get_uint8(x_11, sizeof(void*)*1 + 6);
lean_inc(x_32);
lean_dec(x_11);
x_36 = 1;
x_37 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1 + 1, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1 + 2, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1 + 3, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1 + 4, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*1 + 5, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*1 + 6, x_35);
lean_ctor_set(x_8, 0, x_37);
x_38 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_8, x_5);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_40, x_7);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_46 = x_38;
} else {
 lean_dec_ref(x_38);
 x_46 = lean_box(0);
}
lean_inc(x_3);
x_47 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_44);
x_48 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_45, x_7);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_50 = lean_ctor_get(x_8, 0);
x_51 = lean_ctor_get(x_8, 1);
x_52 = lean_ctor_get(x_8, 2);
x_53 = lean_ctor_get(x_8, 3);
x_54 = lean_ctor_get(x_8, 4);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_8);
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
x_56 = lean_ctor_get_uint8(x_50, sizeof(void*)*1 + 4);
x_57 = lean_ctor_get_uint8(x_50, sizeof(void*)*1 + 5);
x_58 = lean_ctor_get_uint8(x_50, sizeof(void*)*1 + 6);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_59 = x_50;
} else {
 lean_dec_ref(x_50);
 x_59 = lean_box(0);
}
x_60 = 1;
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 1, 7);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*1 + 1, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*1 + 2, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*1 + 3, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*1 + 4, x_56);
lean_ctor_set_uint8(x_61, sizeof(void*)*1 + 5, x_57);
lean_ctor_set_uint8(x_61, sizeof(void*)*1 + 6, x_58);
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_51);
lean_ctor_set(x_62, 2, x_52);
lean_ctor_set(x_62, 3, x_53);
lean_ctor_set(x_62, 4, x_54);
x_63 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_62, x_5);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_65, x_7);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_71 = x_63;
} else {
 lean_dec_ref(x_63);
 x_71 = lean_box(0);
}
lean_inc(x_3);
x_72 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_69);
x_73 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_70, x_7);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_75 = lean_ctor_get(x_5, 0);
x_76 = lean_ctor_get(x_5, 1);
x_77 = lean_ctor_get(x_5, 2);
x_78 = lean_ctor_get(x_5, 3);
x_79 = lean_ctor_get(x_5, 4);
x_80 = lean_ctor_get(x_5, 5);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_5);
x_81 = lean_ctor_get(x_3, 0);
lean_inc(x_81);
x_82 = l_Lean_TraceState_Inhabited___closed__1;
x_83 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_83, 0, x_75);
lean_ctor_set(x_83, 1, x_76);
lean_ctor_set(x_83, 2, x_77);
lean_ctor_set(x_83, 3, x_78);
lean_ctor_set(x_83, 4, x_82);
lean_ctor_set(x_83, 5, x_80);
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_81, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_81, 3);
lean_inc(x_87);
x_88 = lean_ctor_get(x_81, 4);
lean_inc(x_88);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 lean_ctor_release(x_81, 2);
 lean_ctor_release(x_81, 3);
 lean_ctor_release(x_81, 4);
 x_89 = x_81;
} else {
 lean_dec_ref(x_81);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get_uint8(x_84, sizeof(void*)*1 + 4);
x_92 = lean_ctor_get_uint8(x_84, sizeof(void*)*1 + 5);
x_93 = lean_ctor_get_uint8(x_84, sizeof(void*)*1 + 6);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_94 = x_84;
} else {
 lean_dec_ref(x_84);
 x_94 = lean_box(0);
}
x_95 = 1;
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 1, 7);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_90);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_95);
lean_ctor_set_uint8(x_96, sizeof(void*)*1 + 1, x_95);
lean_ctor_set_uint8(x_96, sizeof(void*)*1 + 2, x_95);
lean_ctor_set_uint8(x_96, sizeof(void*)*1 + 3, x_95);
lean_ctor_set_uint8(x_96, sizeof(void*)*1 + 4, x_91);
lean_ctor_set_uint8(x_96, sizeof(void*)*1 + 5, x_92);
lean_ctor_set_uint8(x_96, sizeof(void*)*1 + 6, x_93);
if (lean_is_scalar(x_89)) {
 x_97 = lean_alloc_ctor(0, 5, 0);
} else {
 x_97 = x_89;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_85);
lean_ctor_set(x_97, 2, x_86);
lean_ctor_set(x_97, 3, x_87);
lean_ctor_set(x_97, 4, x_88);
x_98 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_97, x_83);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
x_102 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_100, x_79);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_106 = x_98;
} else {
 lean_dec_ref(x_98);
 x_106 = lean_box(0);
}
lean_inc(x_3);
x_107 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_104);
x_108 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_105, x_79);
if (lean_is_scalar(x_106)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_106;
}
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
lean_object* l_Lean_Elab_Term_isLevelDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = l_Lean_Meta_isLevelDefEq(x_1, x_2, x_8, x_5);
lean_dec(x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_12, x_7);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_15, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_3);
x_21 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_19);
x_22 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_20, x_7);
lean_ctor_set(x_10, 1, x_22);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
lean_inc(x_3);
x_25 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_23);
x_26 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_24, x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
x_33 = lean_ctor_get(x_5, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = l_Lean_TraceState_Inhabited___closed__1;
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_33);
x_37 = l_Lean_Meta_isLevelDefEq(x_1, x_2, x_34, x_36);
lean_dec(x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_39, x_32);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
lean_inc(x_3);
x_46 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_43);
x_47 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_44, x_32);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Term_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_8);
x_9 = l_Lean_Meta_inferType(x_1, x_7, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_11, x_6);
lean_ctor_set(x_9, 1, x_12);
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
x_15 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_14, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_18);
x_21 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_19, x_6);
lean_ctor_set(x_9, 1, x_21);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
lean_inc(x_2);
x_24 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_22);
x_25 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_23, x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
x_29 = lean_ctor_get(x_4, 2);
x_30 = lean_ctor_get(x_4, 3);
x_31 = lean_ctor_get(x_4, 4);
x_32 = lean_ctor_get(x_4, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = l_Lean_TraceState_Inhabited___closed__1;
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_32);
x_36 = l_Lean_Meta_inferType(x_1, x_33, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_38, x_31);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
lean_inc(x_2);
x_45 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_42);
x_46 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_43, x_31);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Elab_Term_whnf(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_8);
x_9 = l_Lean_Meta_whnf(x_1, x_7, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_11, x_6);
lean_ctor_set(x_9, 1, x_12);
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
x_15 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_14, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_18);
x_21 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_19, x_6);
lean_ctor_set(x_9, 1, x_21);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
lean_inc(x_2);
x_24 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_22);
x_25 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_23, x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
x_29 = lean_ctor_get(x_4, 2);
x_30 = lean_ctor_get(x_4, 3);
x_31 = lean_ctor_get(x_4, 4);
x_32 = lean_ctor_get(x_4, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = l_Lean_TraceState_Inhabited___closed__1;
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_32);
x_36 = l_Lean_Meta_whnf(x_1, x_33, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_38, x_31);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
lean_inc(x_2);
x_45 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_42);
x_46 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_43, x_31);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Elab_Term_whnfForall(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_8);
x_9 = l_Lean_Meta_whnfForall(x_1, x_7, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_11, x_6);
lean_ctor_set(x_9, 1, x_12);
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
x_15 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_14, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_18);
x_21 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_19, x_6);
lean_ctor_set(x_9, 1, x_21);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
lean_inc(x_2);
x_24 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_22);
x_25 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_23, x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
x_29 = lean_ctor_get(x_4, 2);
x_30 = lean_ctor_get(x_4, 3);
x_31 = lean_ctor_get(x_4, 4);
x_32 = lean_ctor_get(x_4, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = l_Lean_TraceState_Inhabited___closed__1;
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_32);
x_36 = l_Lean_Meta_whnfForall(x_1, x_33, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_38, x_31);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
lean_inc(x_2);
x_45 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_42);
x_46 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_43, x_31);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Elab_Term_whnfCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_8);
x_9 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_1, x_7, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_11, x_6);
lean_ctor_set(x_9, 1, x_12);
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
x_15 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_14, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_18);
x_21 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_19, x_6);
lean_ctor_set(x_9, 1, x_21);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
lean_inc(x_2);
x_24 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_22);
x_25 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_23, x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
x_29 = lean_ctor_get(x_4, 2);
x_30 = lean_ctor_get(x_4, 3);
x_31 = lean_ctor_get(x_4, 4);
x_32 = lean_ctor_get(x_4, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = l_Lean_TraceState_Inhabited___closed__1;
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_32);
x_36 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_1, x_33, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_38, x_31);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
lean_inc(x_2);
x_45 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_42);
x_46 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_43, x_31);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Elab_Term_unfoldDefinition_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_8);
x_9 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_1, x_7, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_11, x_6);
lean_ctor_set(x_9, 1, x_12);
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
x_15 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_14, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_18);
x_21 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_19, x_6);
lean_ctor_set(x_9, 1, x_21);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
lean_inc(x_2);
x_24 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_22);
x_25 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_23, x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
x_29 = lean_ctor_get(x_4, 2);
x_30 = lean_ctor_get(x_4, 3);
x_31 = lean_ctor_get(x_4, 4);
x_32 = lean_ctor_get(x_4, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = l_Lean_TraceState_Inhabited___closed__1;
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_32);
x_36 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_1, x_33, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_38, x_31);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
lean_inc(x_2);
x_45 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_42);
x_46 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_43, x_31);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_8);
x_9 = l_Lean_Meta_instantiateMVars(x_1, x_7, x_4);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_11, x_6);
lean_ctor_set(x_9, 1, x_12);
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
x_15 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_14, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_ctor_get(x_4, 3);
x_21 = lean_ctor_get(x_4, 4);
x_22 = lean_ctor_get(x_4, 5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = l_Lean_TraceState_Inhabited___closed__1;
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_19);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set(x_25, 5, x_22);
x_26 = l_Lean_Meta_instantiateMVars(x_1, x_23, x_25);
lean_dec(x_23);
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
x_30 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_28, x_21);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
lean_object* l_Lean_Elab_Term_instantiateLevelMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_8);
x_9 = l_Lean_Meta_instantiateLevelMVars(x_1, x_7, x_4);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_11, x_6);
lean_ctor_set(x_9, 1, x_12);
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
x_15 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_14, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_ctor_get(x_4, 3);
x_21 = lean_ctor_get(x_4, 4);
x_22 = lean_ctor_get(x_4, 5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = l_Lean_TraceState_Inhabited___closed__1;
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_19);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set(x_25, 5, x_22);
x_26 = l_Lean_Meta_instantiateLevelMVars(x_1, x_23, x_25);
lean_dec(x_23);
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
x_30 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_28, x_21);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
lean_object* l_Lean_Elab_Term_isClass(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_8);
x_9 = l_Lean_Meta_isClass(x_1, x_7, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_11, x_6);
lean_ctor_set(x_9, 1, x_12);
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
x_15 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_14, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_18);
x_21 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_19, x_6);
lean_ctor_set(x_9, 1, x_21);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
lean_inc(x_2);
x_24 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_22);
x_25 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_23, x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
x_29 = lean_ctor_get(x_4, 2);
x_30 = lean_ctor_get(x_4, 3);
x_31 = lean_ctor_get(x_4, 4);
x_32 = lean_ctor_get(x_4, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = l_Lean_TraceState_Inhabited___closed__1;
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_32);
x_36 = l_Lean_Meta_isClass(x_1, x_33, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_38, x_31);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
lean_inc(x_2);
x_45 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_42);
x_46 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_43, x_31);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 4);
x_6 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_3, 4, x_6);
x_7 = l_Lean_Meta_mkFreshId___rarg(x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_2, x_9, x_5);
lean_ctor_set(x_7, 1, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_2, x_12, x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 2);
x_18 = lean_ctor_get(x_3, 3);
x_19 = lean_ctor_get(x_3, 4);
x_20 = lean_ctor_get(x_3, 5);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_21 = l_Lean_TraceState_Inhabited___closed__1;
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_18);
lean_ctor_set(x_22, 4, x_21);
lean_ctor_set(x_22, 5, x_20);
x_23 = l_Lean_Meta_mkFreshId___rarg(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_2, x_25, x_19);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 4);
x_6 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_3, 4, x_6);
x_7 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_2, x_9, x_5);
lean_ctor_set(x_7, 1, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_2, x_12, x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 2);
x_18 = lean_ctor_get(x_3, 3);
x_19 = lean_ctor_get(x_3, 4);
x_20 = lean_ctor_get(x_3, 5);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_21 = l_Lean_TraceState_Inhabited___closed__1;
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_18);
lean_ctor_set(x_22, 4, x_21);
lean_ctor_set(x_22, 5, x_20);
x_23 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_2, x_25, x_19);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshExprMVar(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_6, 4, x_10);
x_11 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_mkSort(x_12);
x_15 = lean_box(0);
x_16 = 0;
lean_inc(x_9);
x_17 = l_Lean_Meta_mkFreshExprMVar(x_14, x_15, x_16, x_9, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_mkFreshExprMVar(x_18, x_3, x_2, x_9, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 1);
x_23 = l___private_Lean_Elab_Term_3__fromMetaState(x_4, x_5, x_22, x_8);
lean_ctor_set(x_20, 1, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = l___private_Lean_Elab_Term_3__fromMetaState(x_4, x_5, x_25, x_8);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_28 = lean_ctor_get(x_6, 0);
x_29 = lean_ctor_get(x_6, 1);
x_30 = lean_ctor_get(x_6, 2);
x_31 = lean_ctor_get(x_6, 3);
x_32 = lean_ctor_get(x_6, 4);
x_33 = lean_ctor_get(x_6, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_6);
x_34 = lean_ctor_get(x_4, 0);
lean_inc(x_34);
x_35 = l_Lean_TraceState_Inhabited___closed__1;
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_33);
x_37 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_mkSort(x_38);
x_41 = lean_box(0);
x_42 = 0;
lean_inc(x_34);
x_43 = l_Lean_Meta_mkFreshExprMVar(x_40, x_41, x_42, x_34, x_39);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Meta_mkFreshExprMVar(x_44, x_3, x_2, x_34, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l___private_Lean_Elab_Term_3__fromMetaState(x_4, x_5, x_48, x_32);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_5, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_52, 4);
x_56 = lean_ctor_get(x_4, 0);
lean_inc(x_56);
x_57 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_52, 4, x_57);
x_58 = l_Lean_Meta_mkFreshExprMVar(x_53, x_3, x_2, x_56, x_52);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 1);
x_61 = l___private_Lean_Elab_Term_3__fromMetaState(x_4, x_5, x_60, x_55);
lean_ctor_set(x_58, 1, x_61);
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_58, 0);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_58);
x_64 = l___private_Lean_Elab_Term_3__fromMetaState(x_4, x_5, x_63, x_55);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_66 = lean_ctor_get(x_52, 0);
x_67 = lean_ctor_get(x_52, 1);
x_68 = lean_ctor_get(x_52, 2);
x_69 = lean_ctor_get(x_52, 3);
x_70 = lean_ctor_get(x_52, 4);
x_71 = lean_ctor_get(x_52, 5);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_52);
x_72 = lean_ctor_get(x_4, 0);
lean_inc(x_72);
x_73 = l_Lean_TraceState_Inhabited___closed__1;
x_74 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_74, 0, x_66);
lean_ctor_set(x_74, 1, x_67);
lean_ctor_set(x_74, 2, x_68);
lean_ctor_set(x_74, 3, x_69);
lean_ctor_set(x_74, 4, x_73);
lean_ctor_set(x_74, 5, x_71);
x_75 = l_Lean_Meta_mkFreshExprMVar(x_53, x_3, x_2, x_72, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = l___private_Lean_Elab_Term_3__fromMetaState(x_4, x_5, x_77, x_70);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshExprMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_Term_mkFreshExprMVar(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_mkFreshExprMVarWithId(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_9 = lean_ctor_get(x_7, 4);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_7, 4, x_11);
x_12 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_mkSort(x_13);
x_16 = lean_box(0);
x_17 = 0;
lean_inc(x_10);
x_18 = l_Lean_Meta_mkFreshExprMVar(x_15, x_16, x_17, x_10, x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_mkFreshExprMVarWithId(x_1, x_19, x_4, x_3, x_10, x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_6, x_23, x_9);
lean_ctor_set(x_21, 1, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_6, x_26, x_9);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_29 = lean_ctor_get(x_7, 0);
x_30 = lean_ctor_get(x_7, 1);
x_31 = lean_ctor_get(x_7, 2);
x_32 = lean_ctor_get(x_7, 3);
x_33 = lean_ctor_get(x_7, 4);
x_34 = lean_ctor_get(x_7, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_7);
x_35 = lean_ctor_get(x_5, 0);
lean_inc(x_35);
x_36 = l_Lean_TraceState_Inhabited___closed__1;
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_34);
x_38 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_mkSort(x_39);
x_42 = lean_box(0);
x_43 = 0;
lean_inc(x_35);
x_44 = l_Lean_Meta_mkFreshExprMVar(x_41, x_42, x_43, x_35, x_40);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Meta_mkFreshExprMVarWithId(x_1, x_45, x_4, x_3, x_35, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_6, x_49, x_33);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_6, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_53, 4);
x_57 = lean_ctor_get(x_5, 0);
lean_inc(x_57);
x_58 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_53, 4, x_58);
x_59 = l_Lean_Meta_mkFreshExprMVarWithId(x_1, x_54, x_4, x_3, x_57, x_53);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 1);
x_62 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_6, x_61, x_56);
lean_ctor_set(x_59, 1, x_62);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
x_65 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_6, x_64, x_56);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_67 = lean_ctor_get(x_53, 0);
x_68 = lean_ctor_get(x_53, 1);
x_69 = lean_ctor_get(x_53, 2);
x_70 = lean_ctor_get(x_53, 3);
x_71 = lean_ctor_get(x_53, 4);
x_72 = lean_ctor_get(x_53, 5);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_53);
x_73 = lean_ctor_get(x_5, 0);
lean_inc(x_73);
x_74 = l_Lean_TraceState_Inhabited___closed__1;
x_75 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_75, 1, x_68);
lean_ctor_set(x_75, 2, x_69);
lean_ctor_set(x_75, 3, x_70);
lean_ctor_set(x_75, 4, x_74);
lean_ctor_set(x_75, 5, x_72);
x_76 = l_Lean_Meta_mkFreshExprMVarWithId(x_1, x_54, x_4, x_3, x_73, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_6, x_78, x_71);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshExprMVarWithId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Elab_Term_mkFreshExprMVarWithId(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_mkFreshTypeMVar(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_mkSort(x_11);
x_14 = l_Lean_Meta_mkFreshExprMVar(x_13, x_2, x_1, x_8, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_16, x_7);
lean_ctor_set(x_14, 1, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_19, x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
x_24 = lean_ctor_get(x_5, 2);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
x_27 = lean_ctor_get(x_5, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = l_Lean_TraceState_Inhabited___closed__1;
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_25);
lean_ctor_set(x_30, 4, x_29);
lean_ctor_set(x_30, 5, x_27);
x_31 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_mkSort(x_32);
x_35 = l_Lean_Meta_mkFreshExprMVar(x_34, x_2, x_1, x_28, x_33);
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
x_39 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_37, x_26);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshTypeMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Elab_Term_mkFreshTypeMVar(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_getLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_8);
x_9 = l_Lean_Meta_getLevel(x_1, x_7, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_11, x_6);
lean_ctor_set(x_9, 1, x_12);
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
x_15 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_14, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_18);
x_21 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_19, x_6);
lean_ctor_set(x_9, 1, x_21);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
lean_inc(x_2);
x_24 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_22);
x_25 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_23, x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
x_29 = lean_ctor_get(x_4, 2);
x_30 = lean_ctor_get(x_4, 3);
x_31 = lean_ctor_get(x_4, 4);
x_32 = lean_ctor_get(x_4, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = l_Lean_TraceState_Inhabited___closed__1;
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_32);
x_36 = l_Lean_Meta_getLevel(x_1, x_33, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_38, x_31);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
lean_inc(x_2);
x_45 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_42);
x_46 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_43, x_31);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Elab_Term_getLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_8);
x_9 = l_Lean_Meta_getLocalDecl(x_1, x_7, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_11, x_6);
lean_ctor_set(x_9, 1, x_12);
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
x_15 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_14, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_18);
x_21 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_19, x_6);
lean_ctor_set(x_9, 1, x_21);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
lean_inc(x_2);
x_24 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_22);
x_25 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_23, x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
x_29 = lean_ctor_get(x_4, 2);
x_30 = lean_ctor_get(x_4, 3);
x_31 = lean_ctor_get(x_4, 4);
x_32 = lean_ctor_get(x_4, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = l_Lean_TraceState_Inhabited___closed__1;
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_32);
x_36 = l_Lean_Meta_getLocalDecl(x_1, x_33, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_38, x_31);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
lean_inc(x_2);
x_45 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_42);
x_46 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_43, x_31);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Elab_Term_mkForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = l_Lean_Meta_mkForall(x_1, x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_12, x_7);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_15, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_3);
x_21 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_19);
x_22 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_20, x_7);
lean_ctor_set(x_10, 1, x_22);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
lean_inc(x_3);
x_25 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_23);
x_26 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_24, x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
x_33 = lean_ctor_get(x_5, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = l_Lean_TraceState_Inhabited___closed__1;
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_33);
x_37 = l_Lean_Meta_mkForall(x_1, x_2, x_34, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_39, x_32);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
lean_inc(x_3);
x_46 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_43);
x_47 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_44, x_32);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Term_mkForallUsedOnly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = l_Lean_Meta_mkForallUsedOnly(x_1, x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_12, x_7);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_15, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_3);
x_21 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_19);
x_22 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_20, x_7);
lean_ctor_set(x_10, 1, x_22);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
lean_inc(x_3);
x_25 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_23);
x_26 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_24, x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
x_33 = lean_ctor_get(x_5, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = l_Lean_TraceState_Inhabited___closed__1;
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_33);
x_37 = l_Lean_Meta_mkForallUsedOnly(x_1, x_2, x_34, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_39, x_32);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
lean_inc(x_3);
x_46 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_43);
x_47 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_44, x_32);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Term_mkLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = l_Lean_Meta_mkLambda(x_1, x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_12, x_7);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_15, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_3);
x_21 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_19);
x_22 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_20, x_7);
lean_ctor_set(x_10, 1, x_22);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
lean_inc(x_3);
x_25 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_23);
x_26 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_24, x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
x_33 = lean_ctor_get(x_5, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = l_Lean_TraceState_Inhabited___closed__1;
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_33);
x_37 = l_Lean_Meta_mkLambda(x_1, x_2, x_34, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_39, x_32);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
lean_inc(x_3);
x_46 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_43);
x_47 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_44, x_32);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Term_mkLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_mkOptionalNode___closed__2;
x_6 = lean_array_push(x_5, x_1);
x_7 = l_Lean_Elab_Term_mkLambda(x_6, x_2, x_3, x_4);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_trySynthInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_8);
x_9 = l_Lean_Meta_trySynthInstance(x_1, x_7, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_11, x_6);
lean_ctor_set(x_9, 1, x_12);
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
x_15 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_14, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_18);
x_21 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_19, x_6);
lean_ctor_set(x_9, 1, x_21);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
lean_inc(x_2);
x_24 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_22);
x_25 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_23, x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
x_29 = lean_ctor_get(x_4, 2);
x_30 = lean_ctor_get(x_4, 3);
x_31 = lean_ctor_get(x_4, 4);
x_32 = lean_ctor_get(x_4, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = l_Lean_TraceState_Inhabited___closed__1;
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_32);
x_36 = l_Lean_Meta_trySynthInstance(x_1, x_33, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_38, x_31);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
lean_inc(x_2);
x_45 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_42);
x_46 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_43, x_31);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Elab_Term_mkAppM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = l_Lean_Meta_mkAppM(x_1, x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_12, x_7);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_15, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_3);
x_21 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_19);
x_22 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_20, x_7);
lean_ctor_set(x_10, 1, x_22);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
lean_inc(x_3);
x_25 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_23);
x_26 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_24, x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
x_33 = lean_ctor_get(x_5, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = l_Lean_TraceState_Inhabited___closed__1;
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_33);
x_37 = l_Lean_Meta_mkAppM(x_1, x_2, x_34, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_39, x_32);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
lean_inc(x_3);
x_46 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_43);
x_47 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_44, x_32);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Term_mkAppM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_mkAppM(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_mkExpectedTypeHint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = l_Lean_Meta_mkExpectedTypeHint(x_1, x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_12, x_7);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_15, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_3);
x_21 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_19);
x_22 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_20, x_7);
lean_ctor_set(x_10, 1, x_22);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
lean_inc(x_3);
x_25 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_23);
x_26 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_24, x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
x_33 = lean_ctor_get(x_5, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = l_Lean_TraceState_Inhabited___closed__1;
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_33);
x_37 = l_Lean_Meta_mkExpectedTypeHint(x_1, x_2, x_34, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_39, x_32);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
lean_inc(x_3);
x_46 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_43);
x_47 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_44, x_32);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Term_decLevel_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_8);
x_9 = l_Lean_Meta_decLevel_x3f(x_1, x_7, x_4);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_11, x_6);
lean_ctor_set(x_9, 1, x_12);
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
x_15 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_14, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_18);
x_21 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_19, x_6);
lean_ctor_set(x_9, 1, x_21);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
lean_inc(x_2);
x_24 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_22);
x_25 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_23, x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
x_29 = lean_ctor_get(x_4, 2);
x_30 = lean_ctor_get(x_4, 3);
x_31 = lean_ctor_get(x_4, 4);
x_32 = lean_ctor_get(x_4, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = l_Lean_TraceState_Inhabited___closed__1;
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_32);
x_36 = l_Lean_Meta_decLevel_x3f(x_1, x_33, x_35);
lean_dec(x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_38, x_31);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
lean_inc(x_2);
x_45 = l___private_Lean_Elab_Term_2__fromMetaException(x_2, x_42);
x_46 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_3, x_43, x_31);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Elab_Term_decLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Elab_Term_decLevel_x3f(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__3;
x_9 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__6;
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Elab_Term_throwError___rarg(x_11, x_2, x_6);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_4, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
return x_4;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_4);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Lean_Elab_Term_getDecLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Term_getLevel(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_Term_decLevel(x_5, x_2, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
lean_object* l_Lean_Elab_Term_savingMCtx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_67; 
x_4 = l_Lean_Elab_Term_getMCtx___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
x_67 = lean_apply_2(x_1, x_2, x_6);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_68);
x_8 = x_70;
x_9 = x_69;
goto block_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_dec(x_67);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_71);
x_8 = x_73;
x_9 = x_72;
goto block_66;
}
block_66:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 1);
lean_dec(x_15);
lean_ctor_set(x_10, 1, x_5);
if (lean_is_scalar(x_7)) {
 x_16 = lean_alloc_ctor(1, 2, 0);
} else {
 x_16 = x_7;
 lean_ctor_set_tag(x_16, 1);
}
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 2);
x_19 = lean_ctor_get(x_10, 3);
x_20 = lean_ctor_get(x_10, 4);
x_21 = lean_ctor_get(x_10, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_5);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set(x_22, 4, x_20);
lean_ctor_set(x_22, 5, x_21);
lean_ctor_set(x_9, 0, x_22);
if (lean_is_scalar(x_7)) {
 x_23 = lean_alloc_ctor(1, 2, 0);
} else {
 x_23 = x_7;
 lean_ctor_set_tag(x_23, 1);
}
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_24 = lean_ctor_get(x_9, 1);
x_25 = lean_ctor_get(x_9, 2);
x_26 = lean_ctor_get(x_9, 3);
x_27 = lean_ctor_get(x_9, 4);
x_28 = lean_ctor_get(x_9, 5);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_10, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_10, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_10, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_10, 5);
lean_inc(x_33);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 lean_ctor_release(x_10, 4);
 lean_ctor_release(x_10, 5);
 x_34 = x_10;
} else {
 lean_dec_ref(x_10);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 6, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_5);
lean_ctor_set(x_35, 2, x_30);
lean_ctor_set(x_35, 3, x_31);
lean_ctor_set(x_35, 4, x_32);
lean_ctor_set(x_35, 5, x_33);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
lean_ctor_set(x_36, 2, x_25);
lean_ctor_set(x_36, 3, x_26);
lean_ctor_set(x_36, 4, x_27);
lean_ctor_set(x_36, 5, x_28);
if (lean_is_scalar(x_7)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_7;
 lean_ctor_set_tag(x_37, 1);
}
lean_ctor_set(x_37, 0, x_11);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_9, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_8, 0);
lean_inc(x_39);
lean_dec(x_8);
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_9, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_38, 1);
lean_dec(x_43);
lean_ctor_set(x_38, 1, x_5);
if (lean_is_scalar(x_7)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_7;
}
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_9);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_38, 0);
x_46 = lean_ctor_get(x_38, 2);
x_47 = lean_ctor_get(x_38, 3);
x_48 = lean_ctor_get(x_38, 4);
x_49 = lean_ctor_get(x_38, 5);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_38);
x_50 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_5);
lean_ctor_set(x_50, 2, x_46);
lean_ctor_set(x_50, 3, x_47);
lean_ctor_set(x_50, 4, x_48);
lean_ctor_set(x_50, 5, x_49);
lean_ctor_set(x_9, 0, x_50);
if (lean_is_scalar(x_7)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_7;
}
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_9);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_52 = lean_ctor_get(x_9, 1);
x_53 = lean_ctor_get(x_9, 2);
x_54 = lean_ctor_get(x_9, 3);
x_55 = lean_ctor_get(x_9, 4);
x_56 = lean_ctor_get(x_9, 5);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_9);
x_57 = lean_ctor_get(x_38, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_38, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_38, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_38, 4);
lean_inc(x_60);
x_61 = lean_ctor_get(x_38, 5);
lean_inc(x_61);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 x_62 = x_38;
} else {
 lean_dec_ref(x_38);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 6, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_5);
lean_ctor_set(x_63, 2, x_58);
lean_ctor_set(x_63, 3, x_59);
lean_ctor_set(x_63, 4, x_60);
lean_ctor_set(x_63, 5, x_61);
x_64 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_52);
lean_ctor_set(x_64, 2, x_53);
lean_ctor_set(x_64, 3, x_54);
lean_ctor_set(x_64, 4, x_55);
lean_ctor_set(x_64, 5, x_56);
if (lean_is_scalar(x_7)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_7;
}
lean_ctor_set(x_65, 0, x_39);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_savingMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_savingMCtx___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_liftLevelM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 9);
x_7 = lean_ctor_get(x_2, 5);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_7);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 5);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_17);
x_23 = lean_apply_2(x_1, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_3, 5);
lean_dec(x_25);
x_26 = lean_ctor_get(x_3, 4);
lean_dec(x_26);
x_27 = lean_ctor_get(x_3, 3);
lean_dec(x_27);
x_28 = lean_ctor_get(x_3, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_3, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 1);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_ctor_set(x_9, 3, x_33);
lean_ctor_set(x_9, 1, x_34);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_23, 1);
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_inc(x_36);
lean_dec(x_23);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
lean_ctor_set(x_9, 3, x_37);
lean_ctor_set(x_9, 1, x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_3);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_3);
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_23, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_42 = x_23;
} else {
 lean_dec_ref(x_23);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
lean_ctor_set(x_9, 3, x_43);
lean_ctor_set(x_9, 1, x_44);
x_45 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_45, 0, x_9);
lean_ctor_set(x_45, 1, x_10);
lean_ctor_set(x_45, 2, x_11);
lean_ctor_set(x_45, 3, x_12);
lean_ctor_set(x_45, 4, x_13);
lean_ctor_set(x_45, 5, x_14);
if (lean_is_scalar(x_42)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_42;
}
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_free_object(x_9);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_47 = !lean_is_exclusive(x_23);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_23, 0);
x_49 = lean_ctor_get(x_23, 1);
lean_dec(x_49);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set(x_23, 0, x_50);
return x_23;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_23, 0);
lean_inc(x_51);
lean_dec(x_23);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_3);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_9, 0);
x_55 = lean_ctor_get(x_9, 1);
x_56 = lean_ctor_get(x_9, 2);
x_57 = lean_ctor_get(x_9, 3);
x_58 = lean_ctor_get(x_9, 4);
x_59 = lean_ctor_get(x_9, 5);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_9);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_55);
x_61 = lean_apply_2(x_1, x_8, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_62 = x_3;
} else {
 lean_dec_ref(x_3);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_65 = x_61;
} else {
 lean_dec_ref(x_61);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_68, 0, x_54);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_56);
lean_ctor_set(x_68, 3, x_66);
lean_ctor_set(x_68, 4, x_58);
lean_ctor_set(x_68, 5, x_59);
if (lean_is_scalar(x_62)) {
 x_69 = lean_alloc_ctor(0, 6, 0);
} else {
 x_69 = x_62;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_10);
lean_ctor_set(x_69, 2, x_11);
lean_ctor_set(x_69, 3, x_12);
lean_ctor_set(x_69, 4, x_13);
lean_ctor_set(x_69, 5, x_14);
if (lean_is_scalar(x_65)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_65;
}
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_71 = lean_ctor_get(x_61, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_72 = x_61;
} else {
 lean_dec_ref(x_61);
 x_72 = lean_box(0);
}
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_71);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_3);
return x_74;
}
}
}
}
lean_object* l_Lean_Elab_Term_liftLevelM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_liftLevelM___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_liftLevelM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_liftLevelM___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Level_elabLevel), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_Term_liftLevelM___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_elabLevel(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_withConfig___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_apply_1(x_1, x_8);
lean_ctor_set(x_6, 0, x_9);
x_10 = lean_apply_2(x_2, x_3, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
x_13 = lean_ctor_get(x_6, 2);
x_14 = lean_ctor_get(x_6, 3);
x_15 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_16 = lean_apply_1(x_1, x_11);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_14);
lean_ctor_set(x_17, 4, x_15);
lean_ctor_set(x_3, 0, x_17);
x_18 = lean_apply_2(x_2, x_3, x_4);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get(x_3, 2);
x_22 = lean_ctor_get(x_3, 3);
x_23 = lean_ctor_get(x_3, 4);
x_24 = lean_ctor_get(x_3, 5);
x_25 = lean_ctor_get(x_3, 6);
x_26 = lean_ctor_get(x_3, 7);
x_27 = lean_ctor_get(x_3, 8);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_29 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_30 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_31 = lean_ctor_get(x_3, 9);
lean_inc(x_31);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_32 = lean_ctor_get(x_19, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_19, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_19, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_19, 4);
lean_inc(x_36);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 x_37 = x_19;
} else {
 lean_dec_ref(x_19);
 x_37 = lean_box(0);
}
x_38 = lean_apply_1(x_1, x_32);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 5, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_34);
lean_ctor_set(x_39, 3, x_35);
lean_ctor_set(x_39, 4, x_36);
x_40 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_20);
lean_ctor_set(x_40, 2, x_21);
lean_ctor_set(x_40, 3, x_22);
lean_ctor_set(x_40, 4, x_23);
lean_ctor_set(x_40, 5, x_24);
lean_ctor_set(x_40, 6, x_25);
lean_ctor_set(x_40, 7, x_26);
lean_ctor_set(x_40, 8, x_27);
lean_ctor_set(x_40, 9, x_31);
lean_ctor_set_uint8(x_40, sizeof(void*)*10, x_28);
lean_ctor_set_uint8(x_40, sizeof(void*)*10 + 1, x_29);
lean_ctor_set_uint8(x_40, sizeof(void*)*10 + 2, x_30);
x_41 = lean_apply_2(x_2, x_40, x_4);
return x_41;
}
}
}
lean_object* l_Lean_Elab_Term_withConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withConfig___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_withTransparency___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_3, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; 
lean_ctor_set_uint8(x_6, sizeof(void*)*1 + 6, x_1);
x_12 = lean_apply_2(x_2, x_3, x_4);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_15 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
x_16 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 2);
x_17 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
x_18 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 4);
x_19 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 5);
lean_inc(x_13);
lean_dec(x_6);
x_20 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_14);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 1, x_15);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 2, x_16);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 3, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 4, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 5, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 6, x_1);
lean_ctor_set(x_5, 0, x_20);
x_21 = lean_apply_2(x_2, x_3, x_4);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_5, 1);
x_23 = lean_ctor_get(x_5, 2);
x_24 = lean_ctor_get(x_5, 3);
x_25 = lean_ctor_get(x_5, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_26 = lean_ctor_get(x_6, 0);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_28 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
x_29 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 2);
x_30 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
x_31 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 4);
x_32 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_33 = x_6;
} else {
 lean_dec_ref(x_6);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 1, 7);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_27);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 1, x_28);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 2, x_29);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 3, x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 4, x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 5, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 6, x_1);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_22);
lean_ctor_set(x_35, 2, x_23);
lean_ctor_set(x_35, 3, x_24);
lean_ctor_set(x_35, 4, x_25);
lean_ctor_set(x_3, 0, x_35);
x_36 = lean_apply_2(x_2, x_3, x_4);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_37 = lean_ctor_get(x_3, 1);
x_38 = lean_ctor_get(x_3, 2);
x_39 = lean_ctor_get(x_3, 3);
x_40 = lean_ctor_get(x_3, 4);
x_41 = lean_ctor_get(x_3, 5);
x_42 = lean_ctor_get(x_3, 6);
x_43 = lean_ctor_get(x_3, 7);
x_44 = lean_ctor_get(x_3, 8);
x_45 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_46 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_47 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_48 = lean_ctor_get(x_3, 9);
lean_inc(x_48);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_3);
x_49 = lean_ctor_get(x_5, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_5, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_5, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_5, 4);
lean_inc(x_52);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 x_53 = x_5;
} else {
 lean_dec_ref(x_5);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_6, 0);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_56 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
x_57 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 2);
x_58 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
x_59 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 4);
x_60 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_61 = x_6;
} else {
 lean_dec_ref(x_6);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 1, 7);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_54);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_55);
lean_ctor_set_uint8(x_62, sizeof(void*)*1 + 1, x_56);
lean_ctor_set_uint8(x_62, sizeof(void*)*1 + 2, x_57);
lean_ctor_set_uint8(x_62, sizeof(void*)*1 + 3, x_58);
lean_ctor_set_uint8(x_62, sizeof(void*)*1 + 4, x_59);
lean_ctor_set_uint8(x_62, sizeof(void*)*1 + 5, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*1 + 6, x_1);
if (lean_is_scalar(x_53)) {
 x_63 = lean_alloc_ctor(0, 5, 0);
} else {
 x_63 = x_53;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_49);
lean_ctor_set(x_63, 2, x_50);
lean_ctor_set(x_63, 3, x_51);
lean_ctor_set(x_63, 4, x_52);
x_64 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_37);
lean_ctor_set(x_64, 2, x_38);
lean_ctor_set(x_64, 3, x_39);
lean_ctor_set(x_64, 4, x_40);
lean_ctor_set(x_64, 5, x_41);
lean_ctor_set(x_64, 6, x_42);
lean_ctor_set(x_64, 7, x_43);
lean_ctor_set(x_64, 8, x_44);
lean_ctor_set(x_64, 9, x_48);
lean_ctor_set_uint8(x_64, sizeof(void*)*10, x_45);
lean_ctor_set_uint8(x_64, sizeof(void*)*10 + 1, x_46);
lean_ctor_set_uint8(x_64, sizeof(void*)*10 + 2, x_47);
x_65 = lean_apply_2(x_2, x_64, x_4);
return x_65;
}
}
}
lean_object* l_Lean_Elab_Term_withTransparency(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withTransparency___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_withTransparency___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Elab_Term_withTransparency___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_withReducible___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 2;
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 6, x_11);
x_12 = lean_apply_2(x_1, x_2, x_3);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_16 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_17 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_18 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 4);
x_19 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 5);
lean_inc(x_13);
lean_dec(x_5);
x_20 = 2;
x_21 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_14);
lean_ctor_set_uint8(x_21, sizeof(void*)*1 + 1, x_15);
lean_ctor_set_uint8(x_21, sizeof(void*)*1 + 2, x_16);
lean_ctor_set_uint8(x_21, sizeof(void*)*1 + 3, x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*1 + 4, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*1 + 5, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1 + 6, x_20);
lean_ctor_set(x_4, 0, x_21);
x_22 = lean_apply_2(x_1, x_2, x_3);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_ctor_get(x_4, 2);
x_25 = lean_ctor_get(x_4, 3);
x_26 = lean_ctor_get(x_4, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_27 = lean_ctor_get(x_5, 0);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_29 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_30 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_31 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_32 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 4);
x_33 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_34 = x_5;
} else {
 lean_dec_ref(x_5);
 x_34 = lean_box(0);
}
x_35 = 2;
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 1, 7);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_28);
lean_ctor_set_uint8(x_36, sizeof(void*)*1 + 1, x_29);
lean_ctor_set_uint8(x_36, sizeof(void*)*1 + 2, x_30);
lean_ctor_set_uint8(x_36, sizeof(void*)*1 + 3, x_31);
lean_ctor_set_uint8(x_36, sizeof(void*)*1 + 4, x_32);
lean_ctor_set_uint8(x_36, sizeof(void*)*1 + 5, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*1 + 6, x_35);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_23);
lean_ctor_set(x_37, 2, x_24);
lean_ctor_set(x_37, 3, x_25);
lean_ctor_set(x_37, 4, x_26);
lean_ctor_set(x_2, 0, x_37);
x_38 = lean_apply_2(x_1, x_2, x_3);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_39 = lean_ctor_get(x_2, 1);
x_40 = lean_ctor_get(x_2, 2);
x_41 = lean_ctor_get(x_2, 3);
x_42 = lean_ctor_get(x_2, 4);
x_43 = lean_ctor_get(x_2, 5);
x_44 = lean_ctor_get(x_2, 6);
x_45 = lean_ctor_get(x_2, 7);
x_46 = lean_ctor_get(x_2, 8);
x_47 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_48 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_49 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_50 = lean_ctor_get(x_2, 9);
lean_inc(x_50);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
x_51 = lean_ctor_get(x_4, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_4, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_4, 3);
lean_inc(x_53);
x_54 = lean_ctor_get(x_4, 4);
lean_inc(x_54);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_55 = x_4;
} else {
 lean_dec_ref(x_4);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_5, 0);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_58 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_59 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_60 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_61 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 4);
x_62 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_63 = x_5;
} else {
 lean_dec_ref(x_5);
 x_63 = lean_box(0);
}
x_64 = 2;
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 1, 7);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_56);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_57);
lean_ctor_set_uint8(x_65, sizeof(void*)*1 + 1, x_58);
lean_ctor_set_uint8(x_65, sizeof(void*)*1 + 2, x_59);
lean_ctor_set_uint8(x_65, sizeof(void*)*1 + 3, x_60);
lean_ctor_set_uint8(x_65, sizeof(void*)*1 + 4, x_61);
lean_ctor_set_uint8(x_65, sizeof(void*)*1 + 5, x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*1 + 6, x_64);
if (lean_is_scalar(x_55)) {
 x_66 = lean_alloc_ctor(0, 5, 0);
} else {
 x_66 = x_55;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_51);
lean_ctor_set(x_66, 2, x_52);
lean_ctor_set(x_66, 3, x_53);
lean_ctor_set(x_66, 4, x_54);
x_67 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_39);
lean_ctor_set(x_67, 2, x_40);
lean_ctor_set(x_67, 3, x_41);
lean_ctor_set(x_67, 4, x_42);
lean_ctor_set(x_67, 5, x_43);
lean_ctor_set(x_67, 6, x_44);
lean_ctor_set(x_67, 7, x_45);
lean_ctor_set(x_67, 8, x_46);
lean_ctor_set(x_67, 9, x_50);
lean_ctor_set_uint8(x_67, sizeof(void*)*10, x_47);
lean_ctor_set_uint8(x_67, sizeof(void*)*10 + 1, x_48);
lean_ctor_set_uint8(x_67, sizeof(void*)*10 + 2, x_49);
x_68 = lean_apply_2(x_1, x_67, x_3);
return x_68;
}
}
}
lean_object* l_Lean_Elab_Term_withReducible(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withReducible___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_withMacroExpansion___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_4, 7, x_9);
x_10 = lean_apply_2(x_3, x_4, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 4);
x_16 = lean_ctor_get(x_4, 5);
x_17 = lean_ctor_get(x_4, 6);
x_18 = lean_ctor_get(x_4, 7);
x_19 = lean_ctor_get(x_4, 8);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_22 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_23 = lean_ctor_get(x_4, 9);
lean_inc(x_23);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_2);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
x_26 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_12);
lean_ctor_set(x_26, 2, x_13);
lean_ctor_set(x_26, 3, x_14);
lean_ctor_set(x_26, 4, x_15);
lean_ctor_set(x_26, 5, x_16);
lean_ctor_set(x_26, 6, x_17);
lean_ctor_set(x_26, 7, x_25);
lean_ctor_set(x_26, 8, x_19);
lean_ctor_set(x_26, 9, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*10, x_20);
lean_ctor_set_uint8(x_26, sizeof(void*)*10 + 1, x_21);
lean_ctor_set_uint8(x_26, sizeof(void*)*10 + 2, x_22);
x_27 = lean_apply_2(x_3, x_26, x_5);
return x_27;
}
}
}
lean_object* l_Lean_Elab_Term_withMacroExpansion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMacroExpansion___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_registerSyntheticMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 9);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_2);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_4, 1, x_9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_3, 9);
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get(x_4, 3);
x_17 = lean_ctor_get(x_4, 4);
x_18 = lean_ctor_get(x_4, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
lean_inc(x_12);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_19, 2, x_2);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_15);
lean_ctor_set(x_21, 3, x_16);
lean_ctor_set(x_21, 4, x_17);
lean_ctor_set(x_21, 5, x_18);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
lean_object* l_Lean_Elab_Term_registerSyntheticMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_registerSyntheticMVar(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_withoutPostponing___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
lean_ctor_set_uint8(x_2, sizeof(void*)*10, x_5);
x_6 = lean_apply_2(x_1, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_18 = lean_ctor_get(x_2, 9);
lean_inc(x_18);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_19 = 0;
x_20 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_20, 2, x_9);
lean_ctor_set(x_20, 3, x_10);
lean_ctor_set(x_20, 4, x_11);
lean_ctor_set(x_20, 5, x_12);
lean_ctor_set(x_20, 6, x_13);
lean_ctor_set(x_20, 7, x_14);
lean_ctor_set(x_20, 8, x_15);
lean_ctor_set(x_20, 9, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*10, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*10 + 1, x_16);
lean_ctor_set_uint8(x_20, sizeof(void*)*10 + 2, x_17);
x_21 = lean_apply_2(x_1, x_20, x_3);
return x_21;
}
}
}
lean_object* l_Lean_Elab_Term_withoutPostponing(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutPostponing___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkExplicitBinder___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Prod_HasRepr___rarg___closed__1;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkExplicitBinder___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkExplicitBinder___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__9;
x_2 = l_Lean_Elab_Term_mkExplicitBinder___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_mkExplicitBinder___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Option_HasRepr___rarg___closed__3;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkExplicitBinder___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkExplicitBinder___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_mkExplicitBinder___closed__5;
x_2 = l_Lean_Elab_Term_mkExplicitBinder___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_mkExplicitBinder(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_3 = l_Lean_mkOptionalNode___closed__2;
x_4 = lean_array_push(x_3, x_1);
x_5 = l_Lean_nullKind;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Lean_Elab_Term_mkExplicitBinder___closed__3;
x_8 = lean_array_push(x_7, x_2);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Elab_Term_mkExplicitBinder___closed__6;
x_11 = lean_array_push(x_10, x_6);
x_12 = lean_array_push(x_11, x_9);
x_13 = l_Lean_mkOptionalNode___closed__1;
x_14 = lean_array_push(x_12, x_13);
x_15 = l_Lean_Elab_Term_mkExplicitBinder___closed__4;
x_16 = lean_array_push(x_14, x_15);
x_17 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
uint8_t l_Lean_Elab_Term_levelMVarToParam___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 5);
x_4 = l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Term_getMCtx___rarg(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Term_levelMVarToParam___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_3);
x_10 = l_Lean_Closure_mkNewLevelParam___closed__2;
x_11 = l_Lean_MetavarContext_levelMVarToParam(x_7, x_9, x_1, x_10, x_2);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
lean_ctor_set(x_16, 1, x_19);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 2);
x_22 = lean_ctor_get(x_16, 3);
x_23 = lean_ctor_get(x_16, 4);
x_24 = lean_ctor_get(x_16, 5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_25 = lean_ctor_get(x_11, 0);
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set(x_26, 4, x_23);
lean_ctor_set(x_26, 5, x_24);
lean_ctor_set(x_8, 0, x_26);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_27 = lean_ctor_get(x_8, 0);
x_28 = lean_ctor_get(x_8, 1);
x_29 = lean_ctor_get(x_8, 2);
x_30 = lean_ctor_get(x_8, 3);
x_31 = lean_ctor_get(x_8, 4);
x_32 = lean_ctor_get(x_8, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_8);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_27, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_27, 4);
lean_inc(x_36);
x_37 = lean_ctor_get(x_27, 5);
lean_inc(x_37);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 lean_ctor_release(x_27, 3);
 lean_ctor_release(x_27, 4);
 lean_ctor_release(x_27, 5);
 x_38 = x_27;
} else {
 lean_dec_ref(x_27);
 x_38 = lean_box(0);
}
x_39 = lean_ctor_get(x_11, 0);
lean_inc(x_39);
lean_dec(x_11);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 6, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_34);
lean_ctor_set(x_40, 3, x_35);
lean_ctor_set(x_40, 4, x_36);
lean_ctor_set(x_40, 5, x_37);
x_41 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_28);
lean_ctor_set(x_41, 2, x_29);
lean_ctor_set(x_41, 3, x_30);
lean_ctor_set(x_41, 4, x_31);
lean_ctor_set(x_41, 5, x_32);
lean_ctor_set(x_5, 1, x_41);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_42 = lean_ctor_get(x_5, 0);
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_5);
x_44 = lean_alloc_closure((void*)(l_Lean_Elab_Term_levelMVarToParam___lambda__1___boxed), 2, 1);
lean_closure_set(x_44, 0, x_3);
x_45 = l_Lean_Closure_mkNewLevelParam___closed__2;
x_46 = l_Lean_MetavarContext_levelMVarToParam(x_42, x_44, x_1, x_45, x_2);
x_47 = lean_ctor_get(x_46, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 2);
lean_inc(x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_43, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_43, 3);
lean_inc(x_53);
x_54 = lean_ctor_get(x_43, 4);
lean_inc(x_54);
x_55 = lean_ctor_get(x_43, 5);
lean_inc(x_55);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 lean_ctor_release(x_43, 4);
 lean_ctor_release(x_43, 5);
 x_56 = x_43;
} else {
 lean_dec_ref(x_43);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_50, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_50, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_50, 4);
lean_inc(x_60);
x_61 = lean_ctor_get(x_50, 5);
lean_inc(x_61);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 lean_ctor_release(x_50, 3);
 lean_ctor_release(x_50, 4);
 lean_ctor_release(x_50, 5);
 x_62 = x_50;
} else {
 lean_dec_ref(x_50);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_46, 0);
lean_inc(x_63);
lean_dec(x_46);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 6, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_58);
lean_ctor_set(x_64, 3, x_59);
lean_ctor_set(x_64, 4, x_60);
lean_ctor_set(x_64, 5, x_61);
if (lean_is_scalar(x_56)) {
 x_65 = lean_alloc_ctor(0, 6, 0);
} else {
 x_65 = x_56;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_51);
lean_ctor_set(x_65, 2, x_52);
lean_ctor_set(x_65, 3, x_53);
lean_ctor_set(x_65, 4, x_54);
lean_ctor_set(x_65, 5, x_55);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_49);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
lean_object* l_Lean_Elab_Term_levelMVarToParam___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Term_levelMVarToParam___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_levelMVarToParam_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Term_levelMVarToParam(x_1, x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_16 = x_12;
} else {
 lean_dec_ref(x_12);
 x_16 = lean_box(0);
}
if (lean_is_scalar(x_16)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_16;
}
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
lean_object* _init_l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_a");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_mkFreshAnonymousName___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 4);
x_4 = l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__2;
lean_inc(x_3);
x_5 = l_Lean_Name_appendIndexAfter(x_4, x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
lean_dec(x_3);
lean_ctor_set(x_1, 4, x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_ctor_get(x_1, 4);
x_14 = lean_ctor_get(x_1, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_15 = l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__2;
lean_inc(x_13);
x_16 = l_Lean_Name_appendIndexAfter(x_15, x_13);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_12);
lean_ctor_set(x_19, 4, x_18);
lean_ctor_set(x_19, 5, x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshAnonymousName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_mkFreshAnonymousName___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_mkFreshAnonymousName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_mkFreshAnonymousName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_mkFreshAnonymousIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_mkFreshAnonymousName___rarg(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_mkIdentFrom(x_1, x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = l_Lean_mkIdentFrom(x_1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshAnonymousIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_mkFreshAnonymousIdent(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_inst");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_mkFreshInstanceName___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__2;
lean_inc(x_3);
x_5 = l_Lean_Name_appendIndexAfter(x_4, x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
lean_dec(x_3);
lean_ctor_set(x_1, 3, x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_ctor_get(x_1, 4);
x_14 = lean_ctor_get(x_1, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_15 = l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__2;
lean_inc(x_12);
x_16 = l_Lean_Name_appendIndexAfter(x_15, x_12);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_12, x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_18);
lean_ctor_set(x_19, 4, x_13);
lean_ctor_set(x_19, 5, x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshInstanceName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_mkFreshInstanceName___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_mkFreshInstanceName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_mkFreshInstanceName(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Term_4__hasCDot___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = l___private_Lean_Elab_Term_4__hasCDot___main(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_4);
return x_8;
}
}
}
}
uint8_t l___private_Lean_Elab_Term_4__hasCDot___main(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
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
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Term_4__hasCDot___main___spec__1(x_3, x_3, x_8, x_9);
lean_dec(x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Term_4__hasCDot___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Term_4__hasCDot___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Term_4__hasCDot___main___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Term_4__hasCDot___main(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l___private_Lean_Elab_Term_4__hasCDot(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Elab_Term_4__hasCDot___main(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Term_4__hasCDot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Term_4__hasCDot(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Term_5__expandCDot___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = x_2;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_fget(x_2, x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_fset(x_2, x_1, x_12);
x_14 = x_11;
lean_inc(x_4);
x_15 = l___private_Lean_Elab_Term_5__expandCDot___main(x_14, x_3, x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
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
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_1, x_20);
x_22 = x_18;
x_23 = lean_array_fset(x_13, x_1, x_22);
lean_dec(x_1);
x_1 = x_21;
x_2 = x_23;
x_3 = x_19;
x_5 = x_17;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
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
lean_object* _init_l___private_Lean_Elab_Term_5__expandCDot___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_Prim_fopenFlags___closed__12;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Term_5__expandCDot___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_IO_Prim_fopenFlags___closed__12;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Term_5__expandCDot___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_IO_Prim_fopenFlags___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Term_5__expandCDot___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = x_6;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Term_5__expandCDot___main___spec__1), 5, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
x_17 = x_16;
x_18 = lean_apply_3(x_17, x_2, x_3, x_4);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_1, 1, x_22);
lean_ctor_set(x_20, 0, x_1);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_1, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
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
lean_ctor_set(x_1, 1, x_28);
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_1);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_6);
lean_dec(x_5);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_4, x_37);
x_39 = lean_ctor_get(x_3, 0);
lean_inc(x_39);
lean_dec(x_3);
x_40 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_41 = l_Lean_addMacroScope(x_39, x_40, x_4);
x_42 = lean_box(0);
x_43 = l_Lean_SourceInfo_inhabited___closed__1;
x_44 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_45 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_41);
lean_ctor_set(x_45, 3, x_42);
x_46 = l_Array_empty___closed__1;
x_47 = lean_array_push(x_46, x_45);
x_48 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_49 = lean_array_push(x_47, x_48);
x_50 = l_Lean_mkTermIdFromIdent___closed__2;
lean_ctor_set(x_1, 1, x_49);
lean_ctor_set(x_1, 0, x_50);
lean_inc(x_1);
x_51 = lean_array_push(x_2, x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_38);
return x_53;
}
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_dec(x_1);
x_54 = l_Lean_Parser_Term_cdot___elambda__1___closed__2;
x_55 = lean_name_eq(x_5, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = x_6;
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Term_5__expandCDot___main___spec__1), 5, 2);
lean_closure_set(x_58, 0, x_57);
lean_closure_set(x_58, 1, x_56);
x_59 = x_58;
x_60 = lean_apply_3(x_59, x_2, x_3, x_4);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_66 = x_61;
} else {
 lean_dec_ref(x_61);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_5);
lean_ctor_set(x_67, 1, x_64);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
if (lean_is_scalar(x_63)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_63;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_62);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_5);
x_70 = lean_ctor_get(x_60, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_60, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_72 = x_60;
} else {
 lean_dec_ref(x_60);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_6);
lean_dec(x_5);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_add(x_4, x_74);
x_76 = lean_ctor_get(x_3, 0);
lean_inc(x_76);
lean_dec(x_3);
x_77 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_78 = l_Lean_addMacroScope(x_76, x_77, x_4);
x_79 = lean_box(0);
x_80 = l_Lean_SourceInfo_inhabited___closed__1;
x_81 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__2;
x_82 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_78);
lean_ctor_set(x_82, 3, x_79);
x_83 = l_Array_empty___closed__1;
x_84 = lean_array_push(x_83, x_82);
x_85 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_86 = lean_array_push(x_84, x_85);
x_87 = l_Lean_mkTermIdFromIdent___closed__2;
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
lean_inc(x_88);
x_89 = lean_array_push(x_2, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_75);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_2);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_4);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_3);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_1);
lean_ctor_set(x_94, 1, x_2);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_4);
return x_95;
}
}
}
lean_object* l___private_Lean_Elab_Term_5__expandCDot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Term_5__expandCDot___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_expandCDot_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Term_fun___elambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_expandCDot_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_expandCDot_x3f___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_expandCDot_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("=>");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_expandCDot_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandCDot_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l___private_Lean_Elab_Term_4__hasCDot___main(x_1);
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
x_8 = l___private_Lean_Elab_Term_5__expandCDot___main(x_1, x_7, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_12, x_12, x_13, x_7);
lean_dec(x_12);
x_15 = l_Lean_nullKind___closed__2;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_18 = lean_array_push(x_17, x_16);
x_19 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_20 = lean_array_push(x_18, x_19);
x_21 = lean_array_push(x_20, x_11);
x_22 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_8, 0, x_24);
return x_8;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_28, x_28, x_29, x_7);
lean_dec(x_28);
x_31 = l_Lean_nullKind___closed__2;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_34 = lean_array_push(x_33, x_32);
x_35 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_36 = lean_array_push(x_34, x_35);
x_37 = lean_array_push(x_36, x_27);
x_38 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_26);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
return x_8;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_8, 0);
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_8);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshFVarId___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_dec(x_5);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 3);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
x_11 = lean_name_mk_numeral(x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_10, x_12);
lean_dec(x_10);
lean_ctor_set(x_3, 1, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_1);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
lean_inc(x_16);
lean_inc(x_15);
x_17 = lean_name_mk_numeral(x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_16, x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_2, 3, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_1);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_25 = lean_ctor_get(x_2, 4);
x_26 = lean_ctor_get(x_2, 5);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_29 = x_3;
} else {
 lean_dec_ref(x_3);
 x_29 = lean_box(0);
}
lean_inc(x_28);
lean_inc(x_27);
x_30 = lean_name_mk_numeral(x_27, x_28);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_28, x_31);
lean_dec(x_28);
if (lean_is_scalar(x_29)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_29;
}
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_34, 2, x_24);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_25);
lean_ctor_set(x_34, 5, x_26);
lean_ctor_set(x_1, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_1);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = lean_ctor_get(x_1, 4);
x_40 = lean_ctor_get(x_1, 5);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_1);
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_2, 5);
lean_inc(x_45);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_46 = x_2;
} else {
 lean_dec_ref(x_2);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_3, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_49 = x_3;
} else {
 lean_dec_ref(x_3);
 x_49 = lean_box(0);
}
lean_inc(x_48);
lean_inc(x_47);
x_50 = lean_name_mk_numeral(x_47, x_48);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_48, x_51);
lean_dec(x_48);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_49;
}
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
if (lean_is_scalar(x_46)) {
 x_54 = lean_alloc_ctor(0, 6, 0);
} else {
 x_54 = x_46;
}
lean_ctor_set(x_54, 0, x_41);
lean_ctor_set(x_54, 1, x_42);
lean_ctor_set(x_54, 2, x_43);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set(x_54, 4, x_44);
lean_ctor_set(x_54, 5, x_45);
x_55 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_36);
lean_ctor_set(x_55, 2, x_37);
lean_ctor_set(x_55, 3, x_38);
lean_ctor_set(x_55, 4, x_39);
lean_ctor_set(x_55, 5, x_40);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshFVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_mkFreshFVarId___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_mkFreshFVarId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_mkFreshFVarId(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_withLocalDecl___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; 
x_7 = l_Lean_Elab_Term_mkFreshFVarId___rarg(x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 6);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 7);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 8);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_22 = lean_ctor_get(x_5, 9);
lean_inc(x_22);
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
x_26 = lean_ctor_get(x_8, 2);
x_27 = lean_ctor_get(x_8, 3);
x_28 = lean_ctor_get(x_8, 4);
lean_inc(x_3);
lean_inc(x_9);
x_29 = lean_local_ctx_mk_local_decl(x_25, x_9, x_1, x_3, x_2);
x_30 = l_Lean_mkFVar(x_9);
lean_inc(x_5);
x_31 = l_Lean_Elab_Term_isClass(x_3, x_5, x_10);
x_32 = !lean_is_exclusive(x_5);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_5, 9);
lean_dec(x_33);
x_34 = lean_ctor_get(x_5, 8);
lean_dec(x_34);
x_35 = lean_ctor_get(x_5, 7);
lean_dec(x_35);
x_36 = lean_ctor_get(x_5, 6);
lean_dec(x_36);
x_37 = lean_ctor_get(x_5, 5);
lean_dec(x_37);
x_38 = lean_ctor_get(x_5, 4);
lean_dec(x_38);
x_39 = lean_ctor_get(x_5, 3);
lean_dec(x_39);
x_40 = lean_ctor_get(x_5, 2);
lean_dec(x_40);
x_41 = lean_ctor_get(x_5, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_5, 0);
lean_dec(x_42);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_31, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_31, 1);
lean_inc(x_44);
lean_dec(x_31);
lean_ctor_set(x_8, 1, x_29);
x_45 = lean_apply_3(x_4, x_30, x_5, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_dec(x_31);
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
lean_dec(x_43);
lean_inc(x_30);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_30);
x_49 = lean_array_push(x_26, x_48);
lean_ctor_set(x_8, 2, x_49);
lean_ctor_set(x_8, 1, x_29);
x_50 = lean_apply_3(x_4, x_30, x_5, x_46);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_free_object(x_5);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_8);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_31);
if (x_51 == 0)
{
return x_31;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_31, 0);
x_53 = lean_ctor_get(x_31, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_31);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_dec(x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_31, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_31, 1);
lean_inc(x_56);
lean_dec(x_31);
lean_ctor_set(x_8, 1, x_29);
x_57 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_57, 0, x_8);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_12);
lean_ctor_set(x_57, 3, x_13);
lean_ctor_set(x_57, 4, x_14);
lean_ctor_set(x_57, 5, x_15);
lean_ctor_set(x_57, 6, x_16);
lean_ctor_set(x_57, 7, x_17);
lean_ctor_set(x_57, 8, x_18);
lean_ctor_set(x_57, 9, x_22);
lean_ctor_set_uint8(x_57, sizeof(void*)*10, x_19);
lean_ctor_set_uint8(x_57, sizeof(void*)*10 + 1, x_20);
lean_ctor_set_uint8(x_57, sizeof(void*)*10 + 2, x_21);
x_58 = lean_apply_3(x_4, x_30, x_57, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_31, 1);
lean_inc(x_59);
lean_dec(x_31);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
lean_dec(x_55);
lean_inc(x_30);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_30);
x_62 = lean_array_push(x_26, x_61);
lean_ctor_set(x_8, 2, x_62);
lean_ctor_set(x_8, 1, x_29);
x_63 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_63, 0, x_8);
lean_ctor_set(x_63, 1, x_11);
lean_ctor_set(x_63, 2, x_12);
lean_ctor_set(x_63, 3, x_13);
lean_ctor_set(x_63, 4, x_14);
lean_ctor_set(x_63, 5, x_15);
lean_ctor_set(x_63, 6, x_16);
lean_ctor_set(x_63, 7, x_17);
lean_ctor_set(x_63, 8, x_18);
lean_ctor_set(x_63, 9, x_22);
lean_ctor_set_uint8(x_63, sizeof(void*)*10, x_19);
lean_ctor_set_uint8(x_63, sizeof(void*)*10 + 1, x_20);
lean_ctor_set_uint8(x_63, sizeof(void*)*10 + 2, x_21);
x_64 = lean_apply_3(x_4, x_30, x_63, x_59);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_8);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
x_65 = lean_ctor_get(x_31, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_31, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_67 = x_31;
} else {
 lean_dec_ref(x_31);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_8, 0);
x_70 = lean_ctor_get(x_8, 1);
x_71 = lean_ctor_get(x_8, 2);
x_72 = lean_ctor_get(x_8, 3);
x_73 = lean_ctor_get(x_8, 4);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_9);
x_74 = lean_local_ctx_mk_local_decl(x_70, x_9, x_1, x_3, x_2);
x_75 = l_Lean_mkFVar(x_9);
lean_inc(x_5);
x_76 = l_Lean_Elab_Term_isClass(x_3, x_5, x_10);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 lean_ctor_release(x_5, 8);
 lean_ctor_release(x_5, 9);
 x_77 = x_5;
} else {
 lean_dec_ref(x_5);
 x_77 = lean_box(0);
}
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_80, 0, x_69);
lean_ctor_set(x_80, 1, x_74);
lean_ctor_set(x_80, 2, x_71);
lean_ctor_set(x_80, 3, x_72);
lean_ctor_set(x_80, 4, x_73);
if (lean_is_scalar(x_77)) {
 x_81 = lean_alloc_ctor(0, 10, 3);
} else {
 x_81 = x_77;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_11);
lean_ctor_set(x_81, 2, x_12);
lean_ctor_set(x_81, 3, x_13);
lean_ctor_set(x_81, 4, x_14);
lean_ctor_set(x_81, 5, x_15);
lean_ctor_set(x_81, 6, x_16);
lean_ctor_set(x_81, 7, x_17);
lean_ctor_set(x_81, 8, x_18);
lean_ctor_set(x_81, 9, x_22);
lean_ctor_set_uint8(x_81, sizeof(void*)*10, x_19);
lean_ctor_set_uint8(x_81, sizeof(void*)*10 + 1, x_20);
lean_ctor_set_uint8(x_81, sizeof(void*)*10 + 2, x_21);
x_82 = lean_apply_3(x_4, x_75, x_81, x_79);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_ctor_get(x_78, 0);
lean_inc(x_84);
lean_dec(x_78);
lean_inc(x_75);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_75);
x_86 = lean_array_push(x_71, x_85);
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_69);
lean_ctor_set(x_87, 1, x_74);
lean_ctor_set(x_87, 2, x_86);
lean_ctor_set(x_87, 3, x_72);
lean_ctor_set(x_87, 4, x_73);
if (lean_is_scalar(x_77)) {
 x_88 = lean_alloc_ctor(0, 10, 3);
} else {
 x_88 = x_77;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_11);
lean_ctor_set(x_88, 2, x_12);
lean_ctor_set(x_88, 3, x_13);
lean_ctor_set(x_88, 4, x_14);
lean_ctor_set(x_88, 5, x_15);
lean_ctor_set(x_88, 6, x_16);
lean_ctor_set(x_88, 7, x_17);
lean_ctor_set(x_88, 8, x_18);
lean_ctor_set(x_88, 9, x_22);
lean_ctor_set_uint8(x_88, sizeof(void*)*10, x_19);
lean_ctor_set_uint8(x_88, sizeof(void*)*10 + 1, x_20);
lean_ctor_set_uint8(x_88, sizeof(void*)*10 + 2, x_21);
x_89 = lean_apply_3(x_4, x_75, x_88, x_83);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
x_90 = lean_ctor_get(x_76, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_76, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_92 = x_76;
} else {
 lean_dec_ref(x_76);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
}
lean_object* l_Lean_Elab_Term_withLocalDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withLocalDecl___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_withLocalDecl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_Elab_Term_withLocalDecl___rarg(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_withLetDecl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; 
x_7 = l_Lean_Elab_Term_mkFreshFVarId___rarg(x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 6);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 7);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 8);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_22 = lean_ctor_get(x_5, 9);
lean_inc(x_22);
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
x_26 = lean_ctor_get(x_8, 2);
x_27 = lean_ctor_get(x_8, 3);
x_28 = lean_ctor_get(x_8, 4);
lean_inc(x_2);
lean_inc(x_9);
x_29 = lean_local_ctx_mk_let_decl(x_25, x_9, x_1, x_2, x_3);
x_30 = l_Lean_mkFVar(x_9);
lean_inc(x_5);
x_31 = l_Lean_Elab_Term_isClass(x_2, x_5, x_10);
x_32 = !lean_is_exclusive(x_5);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_5, 9);
lean_dec(x_33);
x_34 = lean_ctor_get(x_5, 8);
lean_dec(x_34);
x_35 = lean_ctor_get(x_5, 7);
lean_dec(x_35);
x_36 = lean_ctor_get(x_5, 6);
lean_dec(x_36);
x_37 = lean_ctor_get(x_5, 5);
lean_dec(x_37);
x_38 = lean_ctor_get(x_5, 4);
lean_dec(x_38);
x_39 = lean_ctor_get(x_5, 3);
lean_dec(x_39);
x_40 = lean_ctor_get(x_5, 2);
lean_dec(x_40);
x_41 = lean_ctor_get(x_5, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_5, 0);
lean_dec(x_42);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_31, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_31, 1);
lean_inc(x_44);
lean_dec(x_31);
lean_ctor_set(x_8, 1, x_29);
x_45 = lean_apply_3(x_4, x_30, x_5, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_dec(x_31);
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
lean_dec(x_43);
lean_inc(x_30);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_30);
x_49 = lean_array_push(x_26, x_48);
lean_ctor_set(x_8, 2, x_49);
lean_ctor_set(x_8, 1, x_29);
x_50 = lean_apply_3(x_4, x_30, x_5, x_46);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_free_object(x_5);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_8);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_31);
if (x_51 == 0)
{
return x_31;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_31, 0);
x_53 = lean_ctor_get(x_31, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_31);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_dec(x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_31, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_31, 1);
lean_inc(x_56);
lean_dec(x_31);
lean_ctor_set(x_8, 1, x_29);
x_57 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_57, 0, x_8);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_12);
lean_ctor_set(x_57, 3, x_13);
lean_ctor_set(x_57, 4, x_14);
lean_ctor_set(x_57, 5, x_15);
lean_ctor_set(x_57, 6, x_16);
lean_ctor_set(x_57, 7, x_17);
lean_ctor_set(x_57, 8, x_18);
lean_ctor_set(x_57, 9, x_22);
lean_ctor_set_uint8(x_57, sizeof(void*)*10, x_19);
lean_ctor_set_uint8(x_57, sizeof(void*)*10 + 1, x_20);
lean_ctor_set_uint8(x_57, sizeof(void*)*10 + 2, x_21);
x_58 = lean_apply_3(x_4, x_30, x_57, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_31, 1);
lean_inc(x_59);
lean_dec(x_31);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
lean_dec(x_55);
lean_inc(x_30);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_30);
x_62 = lean_array_push(x_26, x_61);
lean_ctor_set(x_8, 2, x_62);
lean_ctor_set(x_8, 1, x_29);
x_63 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_63, 0, x_8);
lean_ctor_set(x_63, 1, x_11);
lean_ctor_set(x_63, 2, x_12);
lean_ctor_set(x_63, 3, x_13);
lean_ctor_set(x_63, 4, x_14);
lean_ctor_set(x_63, 5, x_15);
lean_ctor_set(x_63, 6, x_16);
lean_ctor_set(x_63, 7, x_17);
lean_ctor_set(x_63, 8, x_18);
lean_ctor_set(x_63, 9, x_22);
lean_ctor_set_uint8(x_63, sizeof(void*)*10, x_19);
lean_ctor_set_uint8(x_63, sizeof(void*)*10 + 1, x_20);
lean_ctor_set_uint8(x_63, sizeof(void*)*10 + 2, x_21);
x_64 = lean_apply_3(x_4, x_30, x_63, x_59);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_8);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
x_65 = lean_ctor_get(x_31, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_31, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_67 = x_31;
} else {
 lean_dec_ref(x_31);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_8, 0);
x_70 = lean_ctor_get(x_8, 1);
x_71 = lean_ctor_get(x_8, 2);
x_72 = lean_ctor_get(x_8, 3);
x_73 = lean_ctor_get(x_8, 4);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_8);
lean_inc(x_2);
lean_inc(x_9);
x_74 = lean_local_ctx_mk_let_decl(x_70, x_9, x_1, x_2, x_3);
x_75 = l_Lean_mkFVar(x_9);
lean_inc(x_5);
x_76 = l_Lean_Elab_Term_isClass(x_2, x_5, x_10);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 lean_ctor_release(x_5, 8);
 lean_ctor_release(x_5, 9);
 x_77 = x_5;
} else {
 lean_dec_ref(x_5);
 x_77 = lean_box(0);
}
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_80, 0, x_69);
lean_ctor_set(x_80, 1, x_74);
lean_ctor_set(x_80, 2, x_71);
lean_ctor_set(x_80, 3, x_72);
lean_ctor_set(x_80, 4, x_73);
if (lean_is_scalar(x_77)) {
 x_81 = lean_alloc_ctor(0, 10, 3);
} else {
 x_81 = x_77;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_11);
lean_ctor_set(x_81, 2, x_12);
lean_ctor_set(x_81, 3, x_13);
lean_ctor_set(x_81, 4, x_14);
lean_ctor_set(x_81, 5, x_15);
lean_ctor_set(x_81, 6, x_16);
lean_ctor_set(x_81, 7, x_17);
lean_ctor_set(x_81, 8, x_18);
lean_ctor_set(x_81, 9, x_22);
lean_ctor_set_uint8(x_81, sizeof(void*)*10, x_19);
lean_ctor_set_uint8(x_81, sizeof(void*)*10 + 1, x_20);
lean_ctor_set_uint8(x_81, sizeof(void*)*10 + 2, x_21);
x_82 = lean_apply_3(x_4, x_75, x_81, x_79);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_ctor_get(x_78, 0);
lean_inc(x_84);
lean_dec(x_78);
lean_inc(x_75);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_75);
x_86 = lean_array_push(x_71, x_85);
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_69);
lean_ctor_set(x_87, 1, x_74);
lean_ctor_set(x_87, 2, x_86);
lean_ctor_set(x_87, 3, x_72);
lean_ctor_set(x_87, 4, x_73);
if (lean_is_scalar(x_77)) {
 x_88 = lean_alloc_ctor(0, 10, 3);
} else {
 x_88 = x_77;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_11);
lean_ctor_set(x_88, 2, x_12);
lean_ctor_set(x_88, 3, x_13);
lean_ctor_set(x_88, 4, x_14);
lean_ctor_set(x_88, 5, x_15);
lean_ctor_set(x_88, 6, x_16);
lean_ctor_set(x_88, 7, x_17);
lean_ctor_set(x_88, 8, x_18);
lean_ctor_set(x_88, 9, x_22);
lean_ctor_set_uint8(x_88, sizeof(void*)*10, x_19);
lean_ctor_set_uint8(x_88, sizeof(void*)*10 + 1, x_20);
lean_ctor_set_uint8(x_88, sizeof(void*)*10 + 2, x_21);
x_89 = lean_apply_3(x_4, x_75, x_88, x_83);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
x_90 = lean_ctor_get(x_76, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_76, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_92 = x_76;
} else {
 lean_dec_ref(x_76);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
}
lean_object* l_Lean_Elab_Term_withLetDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withLetDecl___rarg), 6, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type mismatch");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_29; 
x_29 = l_Lean_MessageData_Inhabited___closed__1;
x_8 = x_29;
goto block_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_ctor_get(x_4, 0);
lean_inc(x_30);
lean_dec(x_4);
x_31 = l_Lean_Elab_Term_getEnv___rarg(x_7);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Elab_Term_getMCtx___rarg(x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Term_getLCtx(x_6, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Elab_Term_getOptions(x_6, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_32);
lean_ctor_set(x_43, 1, x_35);
lean_ctor_set(x_43, 2, x_38);
lean_ctor_set(x_43, 3, x_41);
x_44 = l_Lean_Meta_Exception_mkAppTypeMismatchMessage(x_30, x_3, x_43);
x_45 = l_Lean_MessageData_Inhabited___closed__1;
x_46 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Elab_Term_throwError___rarg(x_46, x_6, x_42);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_5, 0);
x_49 = l_Lean_MessageData_ofList___closed__3;
lean_inc(x_48);
x_50 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
if (lean_obj_tag(x_4) == 0)
{
x_8 = x_50;
goto block_28;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_ctor_get(x_4, 0);
lean_inc(x_51);
lean_dec(x_4);
x_52 = l_Lean_Elab_Term_getEnv___rarg(x_7);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Elab_Term_getMCtx___rarg(x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Elab_Term_getLCtx(x_6, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Elab_Term_getOptions(x_6, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_56);
lean_ctor_set(x_64, 2, x_59);
lean_ctor_set(x_64, 3, x_62);
x_65 = l_Lean_Meta_Exception_mkAppTypeMismatchMessage(x_51, x_3, x_64);
x_66 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_50);
x_67 = l_Lean_Elab_Term_throwError___rarg(x_66, x_6, x_63);
return x_67;
}
}
block_28:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_3);
x_10 = l_Lean_indentExpr(x_9);
x_11 = l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__3;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_MessageData_ofList___closed__3;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_KernelException_toMessageData___closed__12;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_2);
x_18 = l_Lean_indentExpr(x_17);
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
x_21 = l_Lean_KernelException_toMessageData___closed__15;
x_22 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_1);
x_24 = l_Lean_indentExpr(x_23);
x_25 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_8);
x_27 = l_Lean_Elab_Term_throwError___rarg(x_26, x_6, x_7);
return x_27;
}
}
}
lean_object* l_Lean_Elab_Term_throwTypeMismatchError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwTypeMismatchError___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_withoutMacroStackAtErr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
lean_ctor_set_uint8(x_2, sizeof(void*)*10 + 2, x_5);
x_6 = lean_apply_2(x_1, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_18 = lean_ctor_get(x_2, 9);
lean_inc(x_18);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_19 = 0;
x_20 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_20, 2, x_9);
lean_ctor_set(x_20, 3, x_10);
lean_ctor_set(x_20, 4, x_11);
lean_ctor_set(x_20, 5, x_12);
lean_ctor_set(x_20, 6, x_13);
lean_ctor_set(x_20, 7, x_14);
lean_ctor_set(x_20, 8, x_15);
lean_ctor_set(x_20, 9, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*10, x_16);
lean_ctor_set_uint8(x_20, sizeof(void*)*10 + 1, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*10 + 2, x_19);
x_21 = lean_apply_2(x_1, x_20, x_3);
return x_21;
}
}
}
lean_object* l_Lean_Elab_Term_withoutMacroStackAtErr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutMacroStackAtErr___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to synthesize instance");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_synthesizeInstMVarCore___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_synthesizeInstMVarCore___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("synthesized type class instance is not definitionally equal to expression ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_synthesizeInstMVarCore___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_synthesizeInstMVarCore___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inferred by typing rules, synthesized");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_synthesizeInstMVarCore___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_synthesizeInstMVarCore___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_synthesizeInstMVarCore___closed__6;
x_2 = l_Lean_Elab_Term_synthesizeInstMVarCore___closed__9;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inferred");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_synthesizeInstMVarCore___closed__11;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_synthesizeInstMVarCore___closed__12;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lean_Elab_Term_getMVarDecl(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_2);
x_8 = l_Lean_Elab_Term_instantiateMVars(x_7, x_2, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_2);
lean_inc(x_9);
x_11 = l_Lean_Elab_Term_trySynthInstance(x_9, x_2, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_9);
x_15 = l_Lean_indentExpr(x_14);
x_16 = l_Lean_Elab_Term_synthesizeInstMVarCore___closed__3;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Elab_Term_throwError___rarg(x_17, x_2, x_13);
return x_18;
}
case 1:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_9);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
lean_inc(x_1);
x_21 = l_Lean_Elab_Term_isExprMVarAssigned(x_1, x_2, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lean_Elab_Term_assignExprMVar(x_1, x_20, x_2, x_24);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = 1;
x_29 = lean_box(x_28);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = 1;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_dec(x_21);
x_35 = l_Lean_mkMVar(x_1);
lean_inc(x_2);
x_36 = l_Lean_Elab_Term_instantiateMVars(x_35, x_2, x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_2);
lean_inc(x_20);
lean_inc(x_37);
x_39 = l_Lean_Elab_Term_isDefEq(x_37, x_20, x_2, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_20);
x_44 = l_Lean_indentExpr(x_43);
x_45 = l_Lean_Elab_Term_synthesizeInstMVarCore___closed__10;
x_46 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_MessageData_ofList___closed__3;
x_48 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Elab_Term_synthesizeInstMVarCore___closed__13;
x_50 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_37);
x_52 = l_Lean_indentExpr(x_51);
x_53 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Elab_Term_throwError___rarg(x_53, x_2, x_42);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
return x_54;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_54);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_37);
lean_dec(x_20);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_39);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_39, 0);
lean_dec(x_60);
x_61 = 1;
x_62 = lean_box(x_61);
lean_ctor_set(x_39, 0, x_62);
return x_39;
}
else
{
lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_39, 1);
lean_inc(x_63);
lean_dec(x_39);
x_64 = 1;
x_65 = lean_box(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_37);
lean_dec(x_20);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_39);
if (x_67 == 0)
{
return x_39;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_39, 0);
x_69 = lean_ctor_get(x_39, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_39);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
default: 
{
uint8_t x_71; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_11);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_11, 0);
lean_dec(x_72);
x_73 = 0;
x_74 = lean_box(x_73);
lean_ctor_set(x_11, 0, x_74);
return x_11;
}
else
{
lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_11, 1);
lean_inc(x_75);
lean_dec(x_11);
x_76 = 0;
x_77 = lean_box(x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_11);
if (x_79 == 0)
{
return x_11;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_11, 0);
x_81 = lean_ctor_get(x_11, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_11);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_tryCoe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CoeT");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_tryCoe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_tryCoe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_tryCoe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coe");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_tryCoe___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_tryCoe___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_tryCoe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Elab_Term_isDefEq(x_1, x_2, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_2);
x_11 = l_Lean_Elab_Term_getLevel(x_2, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_5);
lean_inc(x_1);
x_14 = l_Lean_Elab_Term_getLevel(x_1, x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_Term_tryCoe___closed__2;
lean_inc(x_19);
x_21 = l_Lean_mkConst(x_20, x_19);
x_22 = l_Lean_Parser_declareBuiltinParser___closed__3;
lean_inc(x_2);
x_23 = lean_array_push(x_22, x_2);
lean_inc(x_3);
x_24 = lean_array_push(x_23, x_3);
lean_inc(x_1);
x_25 = lean_array_push(x_24, x_1);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_25, x_25, x_26, x_21);
lean_dec(x_25);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = 1;
x_30 = lean_box(0);
lean_inc(x_5);
x_31 = l_Lean_Elab_Term_mkFreshExprMVar(x_28, x_29, x_30, x_5, x_16);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Elab_Term_tryCoe___closed__4;
x_35 = l_Lean_mkConst(x_34, x_19);
x_36 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_inc(x_2);
x_37 = lean_array_push(x_36, x_2);
lean_inc(x_1);
x_38 = lean_array_push(x_37, x_1);
lean_inc(x_3);
x_39 = lean_array_push(x_38, x_3);
lean_inc(x_32);
x_40 = lean_array_push(x_39, x_32);
x_41 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_40, x_40, x_26, x_35);
lean_dec(x_40);
x_42 = l_Lean_Expr_mvarId_x21(x_32);
lean_dec(x_32);
x_43 = lean_ctor_get(x_5, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_5, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_5, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_5, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_5, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_5, 5);
lean_inc(x_48);
x_49 = lean_ctor_get(x_5, 6);
lean_inc(x_49);
x_50 = lean_ctor_get(x_5, 7);
lean_inc(x_50);
x_51 = lean_ctor_get(x_5, 8);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_53 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_54 = lean_ctor_get(x_5, 9);
lean_inc(x_54);
x_55 = 0;
x_56 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_56, 0, x_43);
lean_ctor_set(x_56, 1, x_44);
lean_ctor_set(x_56, 2, x_45);
lean_ctor_set(x_56, 3, x_46);
lean_ctor_set(x_56, 4, x_47);
lean_ctor_set(x_56, 5, x_48);
lean_ctor_set(x_56, 6, x_49);
lean_ctor_set(x_56, 7, x_50);
lean_ctor_set(x_56, 8, x_51);
lean_ctor_set(x_56, 9, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*10, x_52);
lean_ctor_set_uint8(x_56, sizeof(void*)*10 + 1, x_53);
lean_ctor_set_uint8(x_56, sizeof(void*)*10 + 2, x_55);
lean_inc(x_56);
lean_inc(x_42);
x_57 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_42, x_56, x_33);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; uint8_t x_59; 
lean_dec(x_5);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_2);
lean_ctor_set(x_61, 2, x_3);
lean_ctor_set(x_61, 3, x_4);
x_62 = l_Lean_Elab_Term_registerSyntheticMVar(x_42, x_61, x_56, x_60);
lean_dec(x_56);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
lean_ctor_set(x_62, 0, x_41);
return x_62;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_41);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_56);
lean_dec(x_42);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_57);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_57, 0);
lean_dec(x_68);
lean_ctor_set(x_57, 0, x_41);
return x_57;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_57, 1);
lean_inc(x_69);
lean_dec(x_57);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_41);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; 
lean_dec(x_56);
lean_dec(x_42);
lean_dec(x_41);
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_57, 1);
lean_inc(x_73);
lean_dec(x_57);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_74, 4);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_2, x_3, x_4, x_76, x_5, x_73);
lean_dec(x_76);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_57, 1);
lean_inc(x_78);
lean_dec(x_57);
x_79 = lean_box(0);
x_80 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_2, x_3, x_4, x_79, x_5, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_57, 1);
lean_inc(x_81);
lean_dec(x_57);
x_82 = lean_box(0);
x_83 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_2, x_3, x_4, x_82, x_5, x_81);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_14);
if (x_84 == 0)
{
return x_14;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_14, 0);
x_86 = lean_ctor_get(x_14, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_14);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_11);
if (x_88 == 0)
{
return x_11;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_11, 0);
x_90 = lean_ctor_get(x_11, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_11);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_7);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_7, 0);
lean_dec(x_93);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_7, 1);
lean_inc(x_94);
lean_dec(x_7);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_3);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_7);
if (x_96 == 0)
{
return x_7;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_7, 0);
x_98 = lean_ctor_get(x_7, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_7);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
lean_object* l___private_Lean_Elab_Term_6__isTypeApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 2;
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 6, x_11);
x_12 = l_Lean_Elab_Term_whnf(x_1, x_2, x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 5)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_13);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_12, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_12, 0, x_28);
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_dec(x_12);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_12);
if (x_32 == 0)
{
return x_12;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_12, 0);
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_12);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_5, 0);
x_37 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_38 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_39 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_40 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_41 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 4);
x_42 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 5);
lean_inc(x_36);
lean_dec(x_5);
x_43 = 2;
x_44 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_37);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 1, x_38);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 2, x_39);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 3, x_40);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 4, x_41);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 5, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 6, x_43);
lean_ctor_set(x_4, 0, x_44);
x_45 = l_Lean_Elab_Term_whnf(x_1, x_2, x_3);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 5)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_46);
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_55 = x_45;
} else {
 lean_dec_ref(x_45);
 x_55 = lean_box(0);
}
x_56 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_45, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_45, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_60 = x_45;
} else {
 lean_dec_ref(x_45);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_62 = lean_ctor_get(x_4, 1);
x_63 = lean_ctor_get(x_4, 2);
x_64 = lean_ctor_get(x_4, 3);
x_65 = lean_ctor_get(x_4, 4);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_4);
x_66 = lean_ctor_get(x_5, 0);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_68 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_69 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_70 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_71 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 4);
x_72 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_73 = x_5;
} else {
 lean_dec_ref(x_5);
 x_73 = lean_box(0);
}
x_74 = 2;
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 1, 7);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_66);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_67);
lean_ctor_set_uint8(x_75, sizeof(void*)*1 + 1, x_68);
lean_ctor_set_uint8(x_75, sizeof(void*)*1 + 2, x_69);
lean_ctor_set_uint8(x_75, sizeof(void*)*1 + 3, x_70);
lean_ctor_set_uint8(x_75, sizeof(void*)*1 + 4, x_71);
lean_ctor_set_uint8(x_75, sizeof(void*)*1 + 5, x_72);
lean_ctor_set_uint8(x_75, sizeof(void*)*1 + 6, x_74);
x_76 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_62);
lean_ctor_set(x_76, 2, x_63);
lean_ctor_set(x_76, 3, x_64);
lean_ctor_set(x_76, 4, x_65);
lean_ctor_set(x_2, 0, x_76);
x_77 = l_Lean_Elab_Term_whnf(x_1, x_2, x_3);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 5)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_dec(x_78);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_78);
x_86 = lean_ctor_get(x_77, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_87 = x_77;
} else {
 lean_dec_ref(x_77);
 x_87 = lean_box(0);
}
x_88 = lean_box(0);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_77, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_77, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_92 = x_77;
} else {
 lean_dec_ref(x_77);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_94 = lean_ctor_get(x_2, 1);
x_95 = lean_ctor_get(x_2, 2);
x_96 = lean_ctor_get(x_2, 3);
x_97 = lean_ctor_get(x_2, 4);
x_98 = lean_ctor_get(x_2, 5);
x_99 = lean_ctor_get(x_2, 6);
x_100 = lean_ctor_get(x_2, 7);
x_101 = lean_ctor_get(x_2, 8);
x_102 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_103 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_104 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_105 = lean_ctor_get(x_2, 9);
lean_inc(x_105);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_2);
x_106 = lean_ctor_get(x_4, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_4, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_4, 3);
lean_inc(x_108);
x_109 = lean_ctor_get(x_4, 4);
lean_inc(x_109);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_110 = x_4;
} else {
 lean_dec_ref(x_4);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_5, 0);
lean_inc(x_111);
x_112 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_113 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_114 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_115 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_116 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 4);
x_117 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_118 = x_5;
} else {
 lean_dec_ref(x_5);
 x_118 = lean_box(0);
}
x_119 = 2;
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 1, 7);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_111);
lean_ctor_set_uint8(x_120, sizeof(void*)*1, x_112);
lean_ctor_set_uint8(x_120, sizeof(void*)*1 + 1, x_113);
lean_ctor_set_uint8(x_120, sizeof(void*)*1 + 2, x_114);
lean_ctor_set_uint8(x_120, sizeof(void*)*1 + 3, x_115);
lean_ctor_set_uint8(x_120, sizeof(void*)*1 + 4, x_116);
lean_ctor_set_uint8(x_120, sizeof(void*)*1 + 5, x_117);
lean_ctor_set_uint8(x_120, sizeof(void*)*1 + 6, x_119);
if (lean_is_scalar(x_110)) {
 x_121 = lean_alloc_ctor(0, 5, 0);
} else {
 x_121 = x_110;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_106);
lean_ctor_set(x_121, 2, x_107);
lean_ctor_set(x_121, 3, x_108);
lean_ctor_set(x_121, 4, x_109);
x_122 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_94);
lean_ctor_set(x_122, 2, x_95);
lean_ctor_set(x_122, 3, x_96);
lean_ctor_set(x_122, 4, x_97);
lean_ctor_set(x_122, 5, x_98);
lean_ctor_set(x_122, 6, x_99);
lean_ctor_set(x_122, 7, x_100);
lean_ctor_set(x_122, 8, x_101);
lean_ctor_set(x_122, 9, x_105);
lean_ctor_set_uint8(x_122, sizeof(void*)*10, x_102);
lean_ctor_set_uint8(x_122, sizeof(void*)*10 + 1, x_103);
lean_ctor_set_uint8(x_122, sizeof(void*)*10 + 2, x_104);
x_123 = l_Lean_Elab_Term_whnf(x_1, x_122, x_3);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 5)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_124, 1);
lean_inc(x_128);
lean_dec(x_124);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
if (lean_is_scalar(x_126)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_126;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_125);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_124);
x_132 = lean_ctor_get(x_123, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_133 = x_123;
} else {
 lean_dec_ref(x_123);
 x_133 = lean_box(0);
}
x_134 = lean_box(0);
if (lean_is_scalar(x_133)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_133;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_132);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_123, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_123, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_138 = x_123;
} else {
 lean_dec_ref(x_123);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
}
lean_object* _init_l___private_Lean_Elab_Term_7__isMonad_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Monad");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Term_7__isMonad_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Term_7__isMonad_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Term_7__isMonad_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 6);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 7);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 8);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_17 = lean_ctor_get(x_2, 9);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_4, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_5);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = 2;
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 6, x_21);
x_22 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_6);
lean_ctor_set(x_22, 2, x_7);
lean_ctor_set(x_22, 3, x_8);
lean_ctor_set(x_22, 4, x_9);
lean_ctor_set(x_22, 5, x_10);
lean_ctor_set(x_22, 6, x_11);
lean_ctor_set(x_22, 7, x_12);
lean_ctor_set(x_22, 8, x_13);
lean_ctor_set(x_22, 9, x_17);
lean_ctor_set_uint8(x_22, sizeof(void*)*10, x_14);
lean_ctor_set_uint8(x_22, sizeof(void*)*10 + 1, x_15);
lean_ctor_set_uint8(x_22, sizeof(void*)*10 + 2, x_16);
x_23 = l_Lean_Elab_Term_whnf(x_1, x_22, x_3);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 5)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_26);
x_29 = lean_array_push(x_28, x_26);
x_30 = l___private_Lean_Elab_Term_7__isMonad_x3f___closed__2;
lean_inc(x_2);
x_31 = l_Lean_Elab_Term_mkAppM(x_30, x_29, x_2, x_25);
lean_dec(x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Elab_Term_trySynthInstance(x_32, x_2, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 1)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_26);
lean_ctor_set(x_39, 1, x_27);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_34, 0, x_40);
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_dec(x_34);
x_42 = lean_ctor_get(x_35, 0);
lean_inc(x_42);
lean_dec(x_35);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_26);
lean_ctor_set(x_43, 1, x_27);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_35);
lean_dec(x_27);
lean_dec(x_26);
x_46 = !lean_is_exclusive(x_34);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_34, 0);
lean_dec(x_47);
x_48 = lean_box(0);
lean_ctor_set(x_34, 0, x_48);
return x_34;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
lean_dec(x_34);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_27);
lean_dec(x_26);
x_52 = !lean_is_exclusive(x_34);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_34, 0);
lean_dec(x_53);
x_54 = lean_box(0);
lean_ctor_set_tag(x_34, 0);
lean_ctor_set(x_34, 0, x_54);
return x_34;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_34, 1);
lean_inc(x_55);
lean_dec(x_34);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_31);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_31, 0);
lean_dec(x_59);
x_60 = lean_box(0);
lean_ctor_set_tag(x_31, 0);
lean_ctor_set(x_31, 0, x_60);
return x_31;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_31, 1);
lean_inc(x_61);
lean_dec(x_31);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_24);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_23);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_23, 0);
lean_dec(x_65);
x_66 = lean_box(0);
lean_ctor_set(x_23, 0, x_66);
return x_23;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_23, 1);
lean_inc(x_67);
lean_dec(x_23);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_23);
if (x_70 == 0)
{
return x_23;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_23, 0);
x_72 = lean_ctor_get(x_23, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_23);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_5, 0);
x_75 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_76 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_77 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_78 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_79 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 4);
x_80 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 5);
lean_inc(x_74);
lean_dec(x_5);
x_81 = 2;
x_82 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_82, 0, x_74);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_75);
lean_ctor_set_uint8(x_82, sizeof(void*)*1 + 1, x_76);
lean_ctor_set_uint8(x_82, sizeof(void*)*1 + 2, x_77);
lean_ctor_set_uint8(x_82, sizeof(void*)*1 + 3, x_78);
lean_ctor_set_uint8(x_82, sizeof(void*)*1 + 4, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*1 + 5, x_80);
lean_ctor_set_uint8(x_82, sizeof(void*)*1 + 6, x_81);
lean_ctor_set(x_4, 0, x_82);
x_83 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_83, 0, x_4);
lean_ctor_set(x_83, 1, x_6);
lean_ctor_set(x_83, 2, x_7);
lean_ctor_set(x_83, 3, x_8);
lean_ctor_set(x_83, 4, x_9);
lean_ctor_set(x_83, 5, x_10);
lean_ctor_set(x_83, 6, x_11);
lean_ctor_set(x_83, 7, x_12);
lean_ctor_set(x_83, 8, x_13);
lean_ctor_set(x_83, 9, x_17);
lean_ctor_set_uint8(x_83, sizeof(void*)*10, x_14);
lean_ctor_set_uint8(x_83, sizeof(void*)*10 + 1, x_15);
lean_ctor_set_uint8(x_83, sizeof(void*)*10 + 2, x_16);
x_84 = l_Lean_Elab_Term_whnf(x_1, x_83, x_3);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 5)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_87);
x_90 = lean_array_push(x_89, x_87);
x_91 = l___private_Lean_Elab_Term_7__isMonad_x3f___closed__2;
lean_inc(x_2);
x_92 = l_Lean_Elab_Term_mkAppM(x_91, x_90, x_2, x_86);
lean_dec(x_90);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_Elab_Term_trySynthInstance(x_93, x_2, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 1)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
lean_dec(x_96);
x_100 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_100, 0, x_87);
lean_ctor_set(x_100, 1, x_88);
lean_ctor_set(x_100, 2, x_99);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
if (lean_is_scalar(x_98)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_98;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_97);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_96);
lean_dec(x_88);
lean_dec(x_87);
x_103 = lean_ctor_get(x_95, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_104 = x_95;
} else {
 lean_dec_ref(x_95);
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
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_88);
lean_dec(x_87);
x_107 = lean_ctor_get(x_95, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_108 = x_95;
} else {
 lean_dec_ref(x_95);
 x_108 = lean_box(0);
}
x_109 = lean_box(0);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_108;
 lean_ctor_set_tag(x_110, 0);
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_2);
x_111 = lean_ctor_get(x_92, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_112 = x_92;
} else {
 lean_dec_ref(x_92);
 x_112 = lean_box(0);
}
x_113 = lean_box(0);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_112;
 lean_ctor_set_tag(x_114, 0);
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_111);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_85);
lean_dec(x_2);
x_115 = lean_ctor_get(x_84, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_116 = x_84;
} else {
 lean_dec_ref(x_84);
 x_116 = lean_box(0);
}
x_117 = lean_box(0);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_2);
x_119 = lean_ctor_get(x_84, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_84, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_121 = x_84;
} else {
 lean_dec_ref(x_84);
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
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_123 = lean_ctor_get(x_4, 1);
x_124 = lean_ctor_get(x_4, 2);
x_125 = lean_ctor_get(x_4, 3);
x_126 = lean_ctor_get(x_4, 4);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_4);
x_127 = lean_ctor_get(x_5, 0);
lean_inc(x_127);
x_128 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_129 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_130 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_131 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_132 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 4);
x_133 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_134 = x_5;
} else {
 lean_dec_ref(x_5);
 x_134 = lean_box(0);
}
x_135 = 2;
if (lean_is_scalar(x_134)) {
 x_136 = lean_alloc_ctor(0, 1, 7);
} else {
 x_136 = x_134;
}
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set_uint8(x_136, sizeof(void*)*1, x_128);
lean_ctor_set_uint8(x_136, sizeof(void*)*1 + 1, x_129);
lean_ctor_set_uint8(x_136, sizeof(void*)*1 + 2, x_130);
lean_ctor_set_uint8(x_136, sizeof(void*)*1 + 3, x_131);
lean_ctor_set_uint8(x_136, sizeof(void*)*1 + 4, x_132);
lean_ctor_set_uint8(x_136, sizeof(void*)*1 + 5, x_133);
lean_ctor_set_uint8(x_136, sizeof(void*)*1 + 6, x_135);
x_137 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_123);
lean_ctor_set(x_137, 2, x_124);
lean_ctor_set(x_137, 3, x_125);
lean_ctor_set(x_137, 4, x_126);
x_138 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_6);
lean_ctor_set(x_138, 2, x_7);
lean_ctor_set(x_138, 3, x_8);
lean_ctor_set(x_138, 4, x_9);
lean_ctor_set(x_138, 5, x_10);
lean_ctor_set(x_138, 6, x_11);
lean_ctor_set(x_138, 7, x_12);
lean_ctor_set(x_138, 8, x_13);
lean_ctor_set(x_138, 9, x_17);
lean_ctor_set_uint8(x_138, sizeof(void*)*10, x_14);
lean_ctor_set_uint8(x_138, sizeof(void*)*10 + 1, x_15);
lean_ctor_set_uint8(x_138, sizeof(void*)*10 + 2, x_16);
x_139 = l_Lean_Elab_Term_whnf(x_1, x_138, x_3);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
if (lean_obj_tag(x_140) == 5)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_144 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_142);
x_145 = lean_array_push(x_144, x_142);
x_146 = l___private_Lean_Elab_Term_7__isMonad_x3f___closed__2;
lean_inc(x_2);
x_147 = l_Lean_Elab_Term_mkAppM(x_146, x_145, x_2, x_141);
lean_dec(x_145);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_Lean_Elab_Term_trySynthInstance(x_148, x_2, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 1)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
lean_dec(x_151);
x_155 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_155, 0, x_142);
lean_ctor_set(x_155, 1, x_143);
lean_ctor_set(x_155, 2, x_154);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
if (lean_is_scalar(x_153)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_153;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_152);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_151);
lean_dec(x_143);
lean_dec(x_142);
x_158 = lean_ctor_get(x_150, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_159 = x_150;
} else {
 lean_dec_ref(x_150);
 x_159 = lean_box(0);
}
x_160 = lean_box(0);
if (lean_is_scalar(x_159)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_159;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_158);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_143);
lean_dec(x_142);
x_162 = lean_ctor_get(x_150, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_163 = x_150;
} else {
 lean_dec_ref(x_150);
 x_163 = lean_box(0);
}
x_164 = lean_box(0);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_163;
 lean_ctor_set_tag(x_165, 0);
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_162);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_2);
x_166 = lean_ctor_get(x_147, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_167 = x_147;
} else {
 lean_dec_ref(x_147);
 x_167 = lean_box(0);
}
x_168 = lean_box(0);
if (lean_is_scalar(x_167)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_167;
 lean_ctor_set_tag(x_169, 0);
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_166);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_140);
lean_dec(x_2);
x_170 = lean_ctor_get(x_139, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_171 = x_139;
} else {
 lean_dec_ref(x_139);
 x_171 = lean_box(0);
}
x_172 = lean_box(0);
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_170);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_2);
x_174 = lean_ctor_get(x_139, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_139, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_176 = x_139;
} else {
 lean_dec_ref(x_139);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
}
}
lean_object* l_Lean_Elab_Term_synthesizeInst(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Term_instantiateMVars(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_2);
lean_inc(x_5);
x_7 = l_Lean_Elab_Term_trySynthInstance(x_5, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_2);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_18);
return x_7;
}
else
{
lean_object* x_19; 
lean_free_object(x_7);
lean_dec(x_9);
x_19 = lean_box(0);
x_11 = x_19;
goto block_17;
}
block_17:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_5);
x_13 = l_Lean_indentExpr(x_12);
x_14 = l_Lean_Elab_Term_synthesizeInstMVarCore___closed__3;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_Term_throwError___rarg(x_15, x_2, x_10);
return x_16;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_5);
lean_dec(x_2);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
lean_dec(x_20);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_20);
x_31 = lean_box(0);
x_22 = x_31;
goto block_28;
}
block_28:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_5);
x_24 = l_Lean_indentExpr(x_23);
x_25 = l_Lean_Elab_Term_synthesizeInstMVarCore___closed__3;
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Elab_Term_throwError___rarg(x_26, x_2, x_21);
return x_27;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_5);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
return x_7;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_7, 0);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_7);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l___private_Lean_Elab_Term_8__tryPureCoe_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Expr_getAppFn___main(x_2);
x_8 = l_Lean_Expr_isMVar(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Expr_getAppFn___main(x_3);
x_10 = l_Lean_Expr_isMVar(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
lean_inc(x_5);
x_12 = l_Lean_Elab_Term_tryCoe(x_2, x_3, x_4, x_11, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_14, 4);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_14, 4, x_19);
x_20 = l_Lean_Meta_mkPure(x_1, x_15, x_18, x_14);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_13, x_23, x_17);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_20, 1, x_24);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_13, x_27, x_17);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_20, 1);
x_33 = lean_ctor_get(x_20, 0);
lean_dec(x_33);
x_34 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_13, x_32, x_17);
lean_ctor_set_tag(x_20, 0);
lean_ctor_set(x_20, 1, x_34);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_dec(x_20);
x_36 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_13, x_35, x_17);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_11);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_14, 0);
x_39 = lean_ctor_get(x_14, 1);
x_40 = lean_ctor_get(x_14, 2);
x_41 = lean_ctor_get(x_14, 3);
x_42 = lean_ctor_get(x_14, 4);
x_43 = lean_ctor_get(x_14, 5);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_14);
x_44 = lean_ctor_get(x_5, 0);
lean_inc(x_44);
x_45 = l_Lean_TraceState_Inhabited___closed__1;
x_46 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_39);
lean_ctor_set(x_46, 2, x_40);
lean_ctor_set(x_46, 3, x_41);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set(x_46, 5, x_43);
x_47 = l_Lean_Meta_mkPure(x_1, x_15, x_44, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_13, x_49, x_42);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_48);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_55 = x_47;
} else {
 lean_dec_ref(x_47);
 x_55 = lean_box(0);
}
x_56 = l___private_Lean_Elab_Term_3__fromMetaState(x_5, x_13, x_54, x_42);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
 lean_ctor_set_tag(x_57, 0);
}
lean_ctor_set(x_57, 0, x_11);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_5);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_12);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_12, 0);
lean_dec(x_59);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_12, 1);
lean_inc(x_60);
lean_dec(x_12);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_11);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_6);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_6);
return x_65;
}
}
}
lean_object* _init_l_Lean_Elab_Term_tryLiftAndCoe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HasMonadLiftT");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_tryLiftAndCoe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_tryLiftAndCoe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_tryLiftAndCoe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("liftM");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_tryLiftAndCoe___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_tryLiftAndCoe___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_tryLiftAndCoe___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("liftCoeM");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_tryLiftAndCoe___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_tryLiftAndCoe___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_tryLiftAndCoe___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_tryLiftAndCoe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_5);
x_7 = l_Lean_Elab_Term_instantiateMVars(x_2, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l___private_Lean_Elab_Term_7__isMonad_x3f(x_1, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Term_tryCoe(x_1, x_8, x_3, x_4, x_5, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 2);
lean_inc(x_18);
lean_dec(x_14);
lean_inc(x_5);
x_19 = l_Lean_Elab_Term_instantiateMVars(x_17, x_5, x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_8);
lean_inc(x_20);
lean_inc(x_16);
x_22 = l___private_Lean_Elab_Term_8__tryPureCoe_x3f(x_16, x_20, x_8, x_3, x_5, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_5);
lean_inc(x_8);
x_25 = l___private_Lean_Elab_Term_6__isTypeApp_x3f(x_8, x_5, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Elab_Term_tryCoe(x_1, x_8, x_3, x_4, x_5, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
lean_inc(x_5);
lean_inc(x_16);
lean_inc(x_31);
x_33 = l_Lean_Elab_Term_isDefEq(x_31, x_16, x_5, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = l_Lean_mkAppStx___closed__9;
lean_inc(x_31);
x_38 = lean_array_push(x_37, x_31);
lean_inc(x_16);
x_39 = lean_array_push(x_38, x_16);
x_40 = l_Lean_Elab_Term_tryLiftAndCoe___closed__2;
lean_inc(x_5);
x_41 = l_Lean_Elab_Term_mkAppM(x_40, x_39, x_5, x_36);
lean_dec(x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_5);
x_44 = l_Lean_Elab_Term_synthesizeInst(x_42, x_5, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_5);
lean_inc(x_32);
x_47 = l_Lean_Elab_Term_getDecLevel(x_32, x_5, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_5);
lean_inc(x_8);
x_50 = l_Lean_Elab_Term_getDecLevel(x_8, x_5, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_5);
lean_inc(x_1);
x_53 = l_Lean_Elab_Term_getDecLevel(x_1, x_5, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Elab_Term_tryLiftAndCoe___closed__4;
lean_inc(x_59);
x_61 = l_Lean_mkConst(x_60, x_59);
x_62 = l_Lean_Elab_Term_mkExplicitBinder___closed__5;
lean_inc(x_31);
x_63 = lean_array_push(x_62, x_31);
lean_inc(x_16);
x_64 = lean_array_push(x_63, x_16);
lean_inc(x_45);
x_65 = lean_array_push(x_64, x_45);
lean_inc(x_32);
x_66 = lean_array_push(x_65, x_32);
lean_inc(x_3);
x_67 = lean_array_push(x_66, x_3);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_67, x_67, x_68, x_61);
lean_dec(x_67);
lean_inc(x_5);
lean_inc(x_69);
x_70 = l_Lean_Elab_Term_inferType(x_69, x_5, x_55);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_5);
lean_inc(x_1);
x_73 = l_Lean_Elab_Term_isDefEq(x_1, x_71, x_5, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_69);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_5);
lean_inc(x_32);
x_77 = l_Lean_Elab_Term_getLevel(x_32, x_5, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_5);
lean_inc(x_20);
x_80 = l_Lean_Elab_Term_getLevel(x_20, x_5, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_56);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Elab_Term_tryCoe___closed__2;
x_86 = l_Lean_mkConst(x_85, x_84);
x_87 = l_Lean_Parser_declareBuiltinParser___closed__3;
lean_inc(x_32);
x_88 = lean_array_push(x_87, x_32);
x_89 = l_Lean_Meta_commitWhen___at___private_Lean_Meta_ExprDefEq_1__isDefEqEta___spec__1___closed__1;
x_90 = lean_array_push(x_88, x_89);
lean_inc(x_20);
x_91 = lean_array_push(x_90, x_20);
x_92 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_91, x_91, x_68, x_86);
lean_dec(x_91);
x_93 = l___private_Lean_Elab_Term_5__expandCDot___main___closed__3;
x_94 = 0;
lean_inc(x_32);
x_95 = l_Lean_mkForall(x_93, x_94, x_32, x_92);
lean_inc(x_5);
x_96 = l_Lean_Elab_Term_synthesizeInst(x_95, x_5, x_82);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Lean_Elab_Term_tryLiftAndCoe___closed__6;
x_100 = l_Lean_mkConst(x_99, x_59);
x_101 = l_Lean_Elab_Term_tryLiftAndCoe___closed__7;
x_102 = lean_array_push(x_101, x_31);
x_103 = lean_array_push(x_102, x_16);
x_104 = lean_array_push(x_103, x_32);
x_105 = lean_array_push(x_104, x_20);
x_106 = lean_array_push(x_105, x_45);
x_107 = lean_array_push(x_106, x_97);
x_108 = lean_array_push(x_107, x_18);
lean_inc(x_3);
x_109 = lean_array_push(x_108, x_3);
x_110 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_109, x_109, x_68, x_100);
lean_dec(x_109);
lean_inc(x_5);
lean_inc(x_110);
x_111 = l_Lean_Elab_Term_inferType(x_110, x_5, x_98);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
lean_inc(x_5);
lean_inc(x_1);
x_114 = l_Lean_Elab_Term_isDefEq(x_1, x_112, x_5, x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_110);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_8);
lean_inc(x_1);
x_119 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_8, x_3, x_4, x_118, x_5, x_117);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_8, x_3, x_4, x_118, x_5, x_120);
return x_121;
}
else
{
uint8_t x_122; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_114);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_114, 0);
lean_dec(x_123);
lean_ctor_set(x_114, 0, x_110);
return x_114;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_114, 1);
lean_inc(x_124);
lean_dec(x_114);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_110);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_110);
x_126 = lean_ctor_get(x_114, 1);
lean_inc(x_126);
lean_dec(x_114);
x_127 = lean_box(0);
x_128 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_8, x_3, x_4, x_127, x_5, x_126);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_110);
x_129 = lean_ctor_get(x_111, 1);
lean_inc(x_129);
lean_dec(x_111);
x_130 = lean_box(0);
x_131 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_8, x_3, x_4, x_130, x_5, x_129);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_59);
lean_dec(x_45);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
x_132 = lean_ctor_get(x_96, 1);
lean_inc(x_132);
lean_dec(x_96);
x_133 = lean_box(0);
x_134 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_8, x_3, x_4, x_133, x_5, x_132);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_78);
lean_dec(x_59);
lean_dec(x_45);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
x_135 = lean_ctor_get(x_80, 1);
lean_inc(x_135);
lean_dec(x_80);
x_136 = lean_box(0);
x_137 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_8, x_3, x_4, x_136, x_5, x_135);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_59);
lean_dec(x_45);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
x_138 = lean_ctor_get(x_77, 1);
lean_inc(x_138);
lean_dec(x_77);
x_139 = lean_box(0);
x_140 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_8, x_3, x_4, x_139, x_5, x_138);
return x_140;
}
}
else
{
uint8_t x_141; 
lean_dec(x_59);
lean_dec(x_45);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_141 = !lean_is_exclusive(x_73);
if (x_141 == 0)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_73, 0);
lean_dec(x_142);
lean_ctor_set(x_73, 0, x_69);
return x_73;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_73, 1);
lean_inc(x_143);
lean_dec(x_73);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_69);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_69);
lean_dec(x_59);
lean_dec(x_45);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
x_145 = lean_ctor_get(x_73, 1);
lean_inc(x_145);
lean_dec(x_73);
x_146 = lean_box(0);
x_147 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_8, x_3, x_4, x_146, x_5, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_69);
lean_dec(x_59);
lean_dec(x_45);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
x_148 = lean_ctor_get(x_70, 1);
lean_inc(x_148);
lean_dec(x_70);
x_149 = lean_box(0);
x_150 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_8, x_3, x_4, x_149, x_5, x_148);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
x_151 = lean_ctor_get(x_53, 1);
lean_inc(x_151);
lean_dec(x_53);
x_152 = lean_box(0);
x_153 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_8, x_3, x_4, x_152, x_5, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
x_154 = lean_ctor_get(x_50, 1);
lean_inc(x_154);
lean_dec(x_50);
x_155 = lean_box(0);
x_156 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_8, x_3, x_4, x_155, x_5, x_154);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_45);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
x_157 = lean_ctor_get(x_47, 1);
lean_inc(x_157);
lean_dec(x_47);
x_158 = lean_box(0);
x_159 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_8, x_3, x_4, x_158, x_5, x_157);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
x_160 = lean_ctor_get(x_44, 1);
lean_inc(x_160);
lean_dec(x_44);
x_161 = lean_box(0);
x_162 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_8, x_3, x_4, x_161, x_5, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
x_163 = lean_ctor_get(x_41, 1);
lean_inc(x_163);
lean_dec(x_41);
x_164 = lean_box(0);
x_165 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_8, x_3, x_4, x_164, x_5, x_163);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
x_166 = lean_ctor_get(x_33, 1);
lean_inc(x_166);
lean_dec(x_33);
x_167 = l_Lean_Elab_Term_tryCoe(x_1, x_8, x_3, x_4, x_5, x_166);
return x_167;
}
}
else
{
uint8_t x_168; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_168 = !lean_is_exclusive(x_33);
if (x_168 == 0)
{
return x_33;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_33, 0);
x_170 = lean_ctor_get(x_33, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_33);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_25);
if (x_172 == 0)
{
return x_25;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_25, 0);
x_174 = lean_ctor_get(x_25, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_25);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_176 = !lean_is_exclusive(x_22);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_22, 0);
lean_dec(x_177);
x_178 = lean_ctor_get(x_23, 0);
lean_inc(x_178);
lean_dec(x_23);
lean_ctor_set(x_22, 0, x_178);
return x_22;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_22, 1);
lean_inc(x_179);
lean_dec(x_22);
x_180 = lean_ctor_get(x_23, 0);
lean_inc(x_180);
lean_dec(x_23);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_10);
if (x_182 == 0)
{
return x_10;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_10, 0);
x_184 = lean_ctor_get(x_10, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_10);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
}
lean_object* l_Lean_Elab_Term_ensureHasTypeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_2);
x_9 = l_Lean_Elab_Term_isDefEqNoConstantApprox(x_2, x_8, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Elab_Term_tryLiftAndCoe(x_8, x_2, x_3, x_4, x_5, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_9, 0);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Elab_Term_inferType(x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = l_Lean_Elab_Term_ensureHasTypeAux(x_1, x_7, x_2, x_9, x_3, x_8);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Term_9__exceptionToSorry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = 0;
x_57 = lean_box(0);
lean_inc(x_3);
x_58 = l_Lean_Elab_Term_mkFreshTypeMVar(x_56, x_57, x_3, x_4);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_5 = x_59;
x_6 = x_60;
goto block_55;
}
else
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_2, 0);
lean_inc(x_61);
lean_dec(x_2);
x_5 = x_61;
x_6 = x_4;
goto block_55;
}
block_55:
{
lean_object* x_7; 
lean_inc(x_5);
x_7 = l_Lean_Elab_Term_getLevel(x_5, x_3, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_mkSorry___closed__2;
x_14 = l_Lean_mkConst(x_13, x_12);
x_15 = l_Lean_Meta_mkSorry___closed__4;
x_16 = l_Lean_mkAppB(x_14, x_5, x_15);
x_17 = lean_ctor_get(x_1, 4);
lean_inc(x_17);
x_18 = l_Lean_MessageData_hasSyntheticSorry___main(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_10, 2);
x_21 = l_Std_PersistentArray_push___rarg(x_20, x_1);
lean_ctor_set(x_10, 2, x_21);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
x_25 = lean_ctor_get(x_10, 3);
x_26 = lean_ctor_get(x_10, 4);
x_27 = lean_ctor_get(x_10, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_28 = l_Std_PersistentArray_push___rarg(x_24, x_1);
x_29 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_23);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
lean_ctor_set(x_29, 5, x_27);
lean_ctor_set(x_7, 1, x_29);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
}
else
{
lean_dec(x_1);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_30 = lean_ctor_get(x_7, 0);
x_31 = lean_ctor_get(x_7, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_7);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Meta_mkSorry___closed__2;
x_35 = l_Lean_mkConst(x_34, x_33);
x_36 = l_Lean_Meta_mkSorry___closed__4;
x_37 = l_Lean_mkAppB(x_35, x_5, x_36);
x_38 = lean_ctor_get(x_1, 4);
lean_inc(x_38);
x_39 = l_Lean_MessageData_hasSyntheticSorry___main(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_31, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_31, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_31, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_31, 5);
lean_inc(x_45);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 lean_ctor_release(x_31, 3);
 lean_ctor_release(x_31, 4);
 lean_ctor_release(x_31, 5);
 x_46 = x_31;
} else {
 lean_dec_ref(x_31);
 x_46 = lean_box(0);
}
x_47 = l_Std_PersistentArray_push___rarg(x_42, x_1);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 6, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_40);
lean_ctor_set(x_48, 1, x_41);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_43);
lean_ctor_set(x_48, 4, x_44);
lean_ctor_set(x_48, 5, x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_37);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_37);
lean_ctor_set(x_50, 1, x_31);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_5);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_7);
if (x_51 == 0)
{
return x_7;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_7, 0);
x_53 = lean_ctor_get(x_7, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_7);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_tryPostpone(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*10);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Term_tryPostpone___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_tryPostpone(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Expr_getAppFn___main(x_1);
x_5 = l_Lean_Expr_isMVar(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_tryPostpone(x_2, x_3);
return x_8;
}
}
}
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_tryPostponeIfMVar(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_tryPostpone(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Lean_Elab_Term_tryPostponeIfMVar(x_5, x_2, x_3);
return x_6;
}
}
}
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Term_10__postponeElabTerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("postpone");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Term_10__postponeElabTerm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l___private_Lean_Elab_Term_10__postponeElabTerm___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Term_10__postponeElabTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = l_Lean_Elab_Term_getOptions(x_3, x_4);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l___private_Lean_Elab_Term_10__postponeElabTerm___closed__2;
x_47 = l_Lean_checkTraceOption(x_44, x_46);
lean_dec(x_44);
if (x_47 == 0)
{
x_5 = x_45;
goto block_42;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_inc(x_1);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_1);
x_49 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_50 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = l_Lean_MessageData_coeOfOptExpr___closed__1;
x_52 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Elab_Term_logTrace(x_46, x_52, x_3, x_45);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_5 = x_54;
goto block_42;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_2, 0);
lean_inc(x_55);
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Elab_Term_logTrace(x_46, x_57, x_3, x_45);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_5 = x_59;
goto block_42;
}
}
block_42:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = 2;
x_7 = lean_box(0);
lean_inc(x_3);
x_8 = l_Lean_Elab_Term_mkFreshExprMVar(x_2, x_6, x_7, x_3, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_mvarId_x21(x_9);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_3, 7);
x_14 = lean_ctor_get(x_3, 9);
lean_inc(x_13);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = l_Lean_Elab_replaceRef(x_1, x_14);
lean_dec(x_14);
lean_dec(x_1);
lean_ctor_set(x_3, 9, x_16);
x_17 = l_Lean_Elab_Term_registerSyntheticMVar(x_11, x_15, x_3, x_10);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_9);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get(x_3, 3);
x_26 = lean_ctor_get(x_3, 4);
x_27 = lean_ctor_get(x_3, 5);
x_28 = lean_ctor_get(x_3, 6);
x_29 = lean_ctor_get(x_3, 7);
x_30 = lean_ctor_get(x_3, 8);
x_31 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_32 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_33 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_34 = lean_ctor_get(x_3, 9);
lean_inc(x_34);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
lean_inc(x_29);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_29);
x_36 = l_Lean_Elab_replaceRef(x_1, x_34);
lean_dec(x_34);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_37, 0, x_22);
lean_ctor_set(x_37, 1, x_23);
lean_ctor_set(x_37, 2, x_24);
lean_ctor_set(x_37, 3, x_25);
lean_ctor_set(x_37, 4, x_26);
lean_ctor_set(x_37, 5, x_27);
lean_ctor_set(x_37, 6, x_28);
lean_ctor_set(x_37, 7, x_29);
lean_ctor_set(x_37, 8, x_30);
lean_ctor_set(x_37, 9, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*10, x_31);
lean_ctor_set_uint8(x_37, sizeof(void*)*10 + 1, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*10 + 2, x_33);
x_38 = l_Lean_Elab_Term_registerSyntheticMVar(x_11, x_35, x_37, x_10);
lean_dec(x_37);
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
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_9);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
}
lean_object* _init_l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected syntax");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = l_Lean_Syntax_prettyPrint(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_MessageData_ofList___closed__3;
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__3;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_Term_throwError___rarg(x_15, x_6, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
x_19 = lean_apply_4(x_17, x_2, x_3, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_20);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
x_29 = l___private_Lean_Elab_Term_9__exceptionToSorry(x_28, x_3, x_6, x_27);
return x_29;
}
}
else
{
lean_dec(x_20);
lean_dec(x_19);
lean_inc(x_1);
{
lean_object* _tmp_4 = x_18;
lean_object* _tmp_6 = x_1;
x_5 = _tmp_4;
x_7 = _tmp_6;
}
goto _start;
}
}
else
{
lean_dec(x_18);
if (x_4 == 0)
{
uint8_t x_31; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_19, 0);
lean_dec(x_32);
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_dec(x_19);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_20);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_19);
x_35 = l___private_Lean_Elab_Term_10__postponeElabTerm(x_2, x_3, x_6, x_1);
return x_35;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Term_11__elabUsingElabFnsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l___private_Lean_Elab_Term_11__elabUsingElabFnsAux(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabUsingElabFns___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabUsingElabFns___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabUsingElabFns___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Term_elabUsingElabFns___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabUsingElabFns___spec__3(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Elab_Term_elabUsingElabFns___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_Term_elabUsingElabFns___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___main___at_Lean_Elab_Term_elabUsingElabFns___spec__6(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Term_elabUsingElabFns___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Term_elabUsingElabFns___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Std_HashMapImp_find_x3f___at_Lean_Elab_Term_elabUsingElabFns___spec__5(x_4, x_2);
lean_dec(x_4);
return x_7;
}
else
{
lean_dec(x_4);
return x_6;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Std_HashMapImp_find_x3f___at_Lean_Elab_Term_elabUsingElabFns___spec__5(x_8, x_2);
lean_dec(x_8);
return x_9;
}
}
}
lean_object* _init_l_Lean_Elab_Term_elabUsingElabFns___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elaboration function for '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabUsingElabFns___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabUsingElabFns___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabUsingElabFns___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabUsingElabFns___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabUsingElabFns___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has not been implemented");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabUsingElabFns___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabUsingElabFns___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabUsingElabFns___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabUsingElabFns___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabUsingElabFns(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Elab_Term_termElabAttribute;
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_PersistentEnvExtension_getState___rarg(x_7, x_9);
lean_dec(x_9);
lean_dec(x_7);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_1);
x_12 = l_Lean_Syntax_getKind(x_1);
x_13 = l_Lean_SMap_find_x3f___at_Lean_Elab_Term_elabUsingElabFns___spec__1(x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Name_toString___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_12);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Elab_Term_elabUsingElabFns___closed__3;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Elab_Term_elabUsingElabFns___closed__6;
x_21 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Elab_Term_throwError___rarg(x_21, x_4, x_5);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
lean_inc(x_5);
x_24 = l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main(x_5, x_1, x_2, x_3, x_23, x_4, x_5);
return x_24;
}
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabUsingElabFns___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabUsingElabFns___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabUsingElabFns___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabUsingElabFns___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Term_elabUsingElabFns___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Term_elabUsingElabFns___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Elab_Term_elabUsingElabFns___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___main___at_Lean_Elab_Term_elabUsingElabFns___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_Term_elabUsingElabFns___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Elab_Term_elabUsingElabFns___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Term_elabUsingElabFns___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_Elab_Term_elabUsingElabFns___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabUsingElabFns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_Term_elabUsingElabFns(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_ReaderT_lift___at_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
lean_object* l_ReaderT_lift___at_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___at_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 5);
lean_dec(x_5);
lean_ctor_set(x_3, 5, x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_ctor_get(x_3, 3);
x_12 = lean_ctor_get(x_3, 4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_10);
lean_ctor_set(x_13, 3, x_11);
lean_ctor_set(x_13, 4, x_12);
lean_ctor_set(x_13, 5, x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 4);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_EStateM_MonadState___closed__2;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___at_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__1;
x_2 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__3___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_monadLog___closed__1;
x_2 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__4;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__4___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_monadLog___closed__1;
x_2 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__6;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getEnv___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__2___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwErrorAt), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwUnsupportedSyntax___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__8;
x_2 = l_Lean_Elab_Term_monadQuotation___closed__1;
x_3 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__3;
x_4 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__9;
x_5 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__5;
x_6 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__7;
x_7 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__10;
x_8 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__11;
x_9 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 4, x_5);
lean_ctor_set(x_9, 5, x_6);
lean_ctor_set(x_9, 6, x_7);
lean_ctor_set(x_9, 7, x_8);
return x_9;
}
}
lean_object* _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__12;
return x_1;
}
}
lean_object* l_ReaderT_lift___at_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_lift___at_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___lambda__4(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
uint8_t l___private_Lean_Elab_Term_12__isExplicit(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Parser_Term_explicit___elambda__1___closed__2;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_Term_12__isExplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Term_12__isExplicit(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l___private_Lean_Elab_Term_13__isExplicitApp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
lean_inc(x_1);
x_2 = l_Lean_Syntax_getKind(x_1);
x_3 = l_Lean_mkAppStx___closed__8;
x_4 = lean_name_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
lean_dec(x_1);
x_8 = l___private_Lean_Elab_Term_12__isExplicit(x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_Term_13__isExplicitApp___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Term_13__isExplicitApp(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Term_14__isLambdaWithImplicit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
lean_inc(x_2);
x_10 = lean_name_mk_string(x_2, x_9);
lean_inc(x_8);
x_11 = l_Lean_Syntax_isOfKind(x_8, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Parser_Term_instBinder___elambda__1___closed__1;
lean_inc(x_2);
x_13 = lean_name_mk_string(x_2, x_12);
x_14 = l_Lean_Syntax_isOfKind(x_8, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_5 = x_16;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_14;
}
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_18 = 1;
return x_18;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Term_14__isLambdaWithImplicit___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__1;
lean_inc(x_2);
x_10 = lean_name_mk_string(x_2, x_9);
lean_inc(x_8);
x_11 = l_Lean_Syntax_isOfKind(x_8, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Parser_Term_instBinder___elambda__1___closed__1;
lean_inc(x_2);
x_13 = lean_name_mk_string(x_2, x_12);
x_14 = l_Lean_Syntax_isOfKind(x_8, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_5 = x_16;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_14;
}
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_18 = 1;
return x_18;
}
}
}
}
uint8_t l___private_Lean_Elab_Term_14__isLambdaWithImplicit(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = l_Lean_Syntax_getArgs(x_1);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(4u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_13 = lean_array_get_size(x_12);
x_14 = l_Lean_mkAppStx___closed__6;
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Term_14__isLambdaWithImplicit___spec__2(x_1, x_14, x_12, x_13, x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
return x_16;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Term_14__isLambdaWithImplicit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Term_14__isLambdaWithImplicit___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Term_14__isLambdaWithImplicit___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Term_14__isLambdaWithImplicit___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Term_14__isLambdaWithImplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Term_14__isLambdaWithImplicit(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_dropTermParens___main(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
lean_inc(x_1);
x_21 = l_Lean_Syntax_isOfKind(x_1, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = 0;
x_2 = x_22;
goto block_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = l_Lean_Syntax_getArgs(x_1);
x_24 = lean_array_get_size(x_23);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(3u);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_24);
x_2 = x_26;
goto block_19;
}
block_19:
{
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
x_5 = l_Lean_nullKind___closed__2;
lean_inc(x_4);
x_6 = l_Lean_Syntax_isOfKind(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_Syntax_getArgs(x_4);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_4, x_11);
x_13 = l_Lean_Syntax_getArg(x_4, x_3);
lean_dec(x_4);
lean_inc(x_13);
x_14 = l_Lean_Syntax_isOfKind(x_13, x_5);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
x_17 = lean_nat_dec_eq(x_16, x_11);
lean_dec(x_16);
if (x_17 == 0)
{
lean_dec(x_12);
return x_1;
}
else
{
lean_dec(x_1);
x_1 = x_12;
goto _start;
}
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_dropTermParens(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_dropTermParens___main(x_1);
return x_2;
}
}
uint8_t l_Lean_Elab_Term_blockImplicitLambda(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_Term_dropTermParens___main(x_1);
lean_inc(x_2);
x_3 = l___private_Lean_Elab_Term_12__isExplicit(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_inc(x_2);
x_4 = l___private_Lean_Elab_Term_13__isExplicitApp(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l___private_Lean_Elab_Term_14__isLambdaWithImplicit(x_2);
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = 1;
return x_7;
}
}
}
lean_object* l_Lean_Elab_Term_blockImplicitLambda___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_blockImplicitLambda(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_useImplicitLambda_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Elab_Term_blockImplicitLambda(x_1);
if (x_5 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = l_Lean_Elab_Term_whnfForall(x_8, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 7)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint64_t x_13; uint8_t x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get_uint64(x_10, sizeof(void*)*3);
x_14 = (uint8_t)((x_13 << 24) >> 61);
x_15 = l_Lean_BinderInfo_isExplicit(x_14);
if (x_15 == 0)
{
lean_ctor_set(x_2, 0, x_10);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
else
{
lean_object* x_16; 
lean_dec(x_10);
lean_free_object(x_2);
x_16 = lean_box(0);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
}
else
{
lean_object* x_17; uint64_t x_18; uint8_t x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get_uint64(x_10, sizeof(void*)*3);
x_19 = (uint8_t)((x_18 << 24) >> 61);
x_20 = l_Lean_BinderInfo_isExplicit(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_ctor_set(x_2, 0, x_10);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
lean_free_object(x_2);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_free_object(x_2);
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_9, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_dec(x_9);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_free_object(x_2);
x_30 = !lean_is_exclusive(x_9);
if (x_30 == 0)
{
return x_9;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_9, 0);
x_32 = lean_ctor_get(x_9, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_9);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
lean_dec(x_2);
x_35 = l_Lean_Elab_Term_whnfForall(x_34, x_3, x_4);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 7)
{
lean_object* x_37; lean_object* x_38; uint64_t x_39; uint8_t x_40; uint8_t x_41; 
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
x_39 = lean_ctor_get_uint64(x_36, sizeof(void*)*3);
x_40 = (uint8_t)((x_39 << 24) >> 61);
x_41 = l_Lean_BinderInfo_isExplicit(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_36);
if (lean_is_scalar(x_38)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_38;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_36);
x_44 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_38;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_37);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_36);
x_46 = lean_ctor_get(x_35, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_47 = x_35;
} else {
 lean_dec_ref(x_35);
 x_47 = lean_box(0);
}
x_48 = lean_box(0);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_35, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_35, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_52 = x_35;
} else {
 lean_dec_ref(x_35);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_3);
lean_dec(x_2);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_4);
return x_55;
}
}
}
lean_object* _init_l_Lean_Elab_Term_elabImplicitLambdaAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("implicitForall");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabImplicitLambdaAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l_Lean_Elab_Term_elabImplicitLambdaAux___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabImplicitLambdaAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
lean_inc(x_5);
x_8 = l_Lean_Elab_Term_elabUsingElabFns(x_1, x_7, x_2, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_5);
x_11 = l_Lean_Elab_Term_mkLambda(x_4, x_9, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Term_getOptions(x_5, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_Elab_Term_elabImplicitLambdaAux___closed__2;
x_19 = l_Lean_checkTraceOption(x_16, x_18);
lean_dec(x_16);
if (x_19 == 0)
{
lean_dec(x_5);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_free_object(x_14);
lean_inc(x_12);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_12);
x_21 = l_Lean_Elab_Term_logTrace(x_18, x_20, x_5, x_17);
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_12);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = l_Lean_Elab_Term_elabImplicitLambdaAux___closed__2;
x_29 = l_Lean_checkTraceOption(x_26, x_28);
lean_dec(x_26);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_5);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_12);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_12);
x_32 = l_Lean_Elab_Term_logTrace(x_28, x_31, x_5, x_27);
lean_dec(x_5);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_12);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
return x_11;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_11, 0);
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_11);
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
lean_dec(x_5);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_8);
if (x_40 == 0)
{
return x_8;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_8, 0);
x_42 = lean_ctor_get(x_8, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_8);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabImplicitLambdaAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_Elab_Term_elabImplicitLambdaAux(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_elabImplicitLambda___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_expr_instantiate1(x_1, x_5);
lean_inc(x_6);
x_9 = l_Lean_Elab_Term_whnfForall(x_8, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_array_push(x_2, x_5);
x_13 = l_Lean_Elab_Term_elabImplicitLambda___main(x_3, x_4, x_10, x_12, x_6, x_11);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabImplicitLambda___main(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint8_t x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_11 = (uint8_t)((x_10 << 24) >> 61);
x_12 = l_Lean_BinderInfo_isExplicit(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_6, 5);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_14, x_15);
lean_ctor_set(x_6, 5, x_16);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_5, 8);
lean_dec(x_18);
lean_ctor_set(x_5, 8, x_14);
x_19 = l_Lean_Elab_Term_getMainModule___rarg(x_6);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_addMacroScope(x_20, x_7, x_23);
x_26 = lean_box(x_2);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabImplicitLambda___main___lambda__1___boxed), 7, 4);
lean_closure_set(x_27, 0, x_9);
lean_closure_set(x_27, 1, x_4);
lean_closure_set(x_27, 2, x_1);
lean_closure_set(x_27, 3, x_26);
x_28 = l_Lean_Elab_Term_withLocalDecl___rarg(x_25, x_11, x_8, x_27, x_5, x_24);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
x_31 = lean_ctor_get(x_5, 2);
x_32 = lean_ctor_get(x_5, 3);
x_33 = lean_ctor_get(x_5, 4);
x_34 = lean_ctor_get(x_5, 5);
x_35 = lean_ctor_get(x_5, 6);
x_36 = lean_ctor_get(x_5, 7);
x_37 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_38 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_39 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_40 = lean_ctor_get(x_5, 9);
lean_inc(x_40);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_41 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_41, 0, x_29);
lean_ctor_set(x_41, 1, x_30);
lean_ctor_set(x_41, 2, x_31);
lean_ctor_set(x_41, 3, x_32);
lean_ctor_set(x_41, 4, x_33);
lean_ctor_set(x_41, 5, x_34);
lean_ctor_set(x_41, 6, x_35);
lean_ctor_set(x_41, 7, x_36);
lean_ctor_set(x_41, 8, x_14);
lean_ctor_set(x_41, 9, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*10, x_37);
lean_ctor_set_uint8(x_41, sizeof(void*)*10 + 1, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*10 + 2, x_39);
x_42 = l_Lean_Elab_Term_getMainModule___rarg(x_6);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Elab_Term_getCurrMacroScope(x_41, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_addMacroScope(x_43, x_7, x_46);
x_49 = lean_box(x_2);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabImplicitLambda___main___lambda__1___boxed), 7, 4);
lean_closure_set(x_50, 0, x_9);
lean_closure_set(x_50, 1, x_4);
lean_closure_set(x_50, 2, x_1);
lean_closure_set(x_50, 3, x_49);
x_51 = l_Lean_Elab_Term_withLocalDecl___rarg(x_48, x_11, x_8, x_50, x_41, x_47);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_52 = lean_ctor_get(x_6, 0);
x_53 = lean_ctor_get(x_6, 1);
x_54 = lean_ctor_get(x_6, 2);
x_55 = lean_ctor_get(x_6, 3);
x_56 = lean_ctor_get(x_6, 4);
x_57 = lean_ctor_get(x_6, 5);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_6);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_57, x_58);
x_60 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_53);
lean_ctor_set(x_60, 2, x_54);
lean_ctor_set(x_60, 3, x_55);
lean_ctor_set(x_60, 4, x_56);
lean_ctor_set(x_60, 5, x_59);
x_61 = lean_ctor_get(x_5, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_5, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_5, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_5, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_5, 4);
lean_inc(x_65);
x_66 = lean_ctor_get(x_5, 5);
lean_inc(x_66);
x_67 = lean_ctor_get(x_5, 6);
lean_inc(x_67);
x_68 = lean_ctor_get(x_5, 7);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_70 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_71 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_72 = lean_ctor_get(x_5, 9);
lean_inc(x_72);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 lean_ctor_release(x_5, 8);
 lean_ctor_release(x_5, 9);
 x_73 = x_5;
} else {
 lean_dec_ref(x_5);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 10, 3);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_61);
lean_ctor_set(x_74, 1, x_62);
lean_ctor_set(x_74, 2, x_63);
lean_ctor_set(x_74, 3, x_64);
lean_ctor_set(x_74, 4, x_65);
lean_ctor_set(x_74, 5, x_66);
lean_ctor_set(x_74, 6, x_67);
lean_ctor_set(x_74, 7, x_68);
lean_ctor_set(x_74, 8, x_57);
lean_ctor_set(x_74, 9, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*10, x_69);
lean_ctor_set_uint8(x_74, sizeof(void*)*10 + 1, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*10 + 2, x_71);
x_75 = l_Lean_Elab_Term_getMainModule___rarg(x_60);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Elab_Term_getCurrMacroScope(x_74, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_addMacroScope(x_76, x_7, x_79);
x_82 = lean_box(x_2);
x_83 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabImplicitLambda___main___lambda__1___boxed), 7, 4);
lean_closure_set(x_83, 0, x_9);
lean_closure_set(x_83, 1, x_4);
lean_closure_set(x_83, 2, x_1);
lean_closure_set(x_83, 3, x_82);
x_84 = l_Lean_Elab_Term_withLocalDecl___rarg(x_81, x_11, x_8, x_83, x_74, x_80);
return x_84;
}
}
else
{
lean_object* x_85; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_85 = l_Lean_Elab_Term_elabImplicitLambdaAux(x_1, x_2, x_3, x_4, x_5, x_6);
return x_85;
}
}
else
{
lean_object* x_86; 
x_86 = l_Lean_Elab_Term_elabImplicitLambdaAux(x_1, x_2, x_3, x_4, x_5, x_6);
return x_86;
}
}
}
lean_object* l_Lean_Elab_Term_elabImplicitLambda___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Elab_Term_elabImplicitLambda___main___lambda__1(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_elabImplicitLambda___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_Elab_Term_elabImplicitLambda___main(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_elabImplicitLambda(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_elabImplicitLambda___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabImplicitLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_Elab_Term_elabImplicitLambda(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* _init_l_Lean_Elab_Term_elabTermAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MessageData_coeOfOptExpr___closed__1;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabTermAux___main(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_ctor_set(x_6, 5, x_10);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_23 = lean_ctor_get(x_5, 9);
x_24 = lean_ctor_get(x_5, 8);
lean_dec(x_24);
lean_inc(x_23);
lean_inc(x_8);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_ctor_set(x_5, 8, x_8);
x_25 = lean_ctor_get(x_12, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_12, 4);
lean_inc(x_26);
x_27 = lean_nat_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_dec(x_5);
x_28 = x_6;
goto block_207;
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
x_208 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_209 = l_Lean_Elab_Term_throwError___rarg(x_208, x_5, x_6);
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
return x_209;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_209, 0);
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_209);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
block_207:
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_55; lean_object* x_56; lean_object* x_61; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_30 = lean_ctor_get(x_12, 4);
lean_dec(x_30);
x_31 = lean_ctor_get(x_12, 3);
lean_dec(x_31);
x_32 = lean_nat_add(x_25, x_9);
lean_dec(x_25);
lean_inc(x_26);
lean_inc(x_32);
lean_ctor_set(x_12, 3, x_32);
lean_inc(x_23);
lean_inc(x_8);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_33 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_13);
lean_ctor_set(x_33, 2, x_14);
lean_ctor_set(x_33, 3, x_15);
lean_ctor_set(x_33, 4, x_16);
lean_ctor_set(x_33, 5, x_17);
lean_ctor_set(x_33, 6, x_18);
lean_ctor_set(x_33, 7, x_19);
lean_ctor_set(x_33, 8, x_8);
lean_ctor_set(x_33, 9, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*10, x_20);
lean_ctor_set_uint8(x_33, sizeof(void*)*10 + 1, x_21);
lean_ctor_set_uint8(x_33, sizeof(void*)*10 + 2, x_22);
x_105 = l_Lean_Elab_Term_getOptions(x_33, x_28);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__2;
x_109 = l_Lean_checkTraceOption(x_106, x_108);
lean_dec(x_106);
if (x_109 == 0)
{
x_61 = x_107;
goto block_104;
}
else
{
lean_object* x_110; 
lean_inc(x_4);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_4);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = l_Lean_Elab_Term_elabTermAux___main___closed__1;
x_112 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
x_113 = l_Lean_Elab_Term_logTrace(x_108, x_112, x_33, x_107);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_61 = x_114;
goto block_104;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_1, 0);
lean_inc(x_115);
x_116 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_118 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_110);
x_120 = l_Lean_Elab_Term_logTrace(x_108, x_119, x_33, x_107);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_61 = x_121;
goto block_104;
}
}
block_54:
{
if (lean_obj_tag(x_34) == 0)
{
lean_dec(x_12);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
if (x_3 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_Elab_Term_elabUsingElabFns(x_4, x_1, x_2, x_33, x_35);
return x_36;
}
else
{
lean_object* x_37; 
lean_inc(x_33);
lean_inc(x_1);
lean_inc(x_4);
x_37 = l_Lean_Elab_Term_useImplicitLambda_x3f(x_4, x_1, x_33, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Elab_Term_elabUsingElabFns(x_4, x_1, x_2, x_33, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_1);
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_43 = l_Array_empty___closed__1;
x_44 = l_Lean_Elab_Term_elabImplicitLambda___main(x_4, x_2, x_42, x_43, x_33, x_41);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_33);
lean_dec(x_4);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_37, 0);
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_37);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_33);
x_49 = lean_ctor_get(x_34, 0);
lean_inc(x_49);
lean_dec(x_34);
lean_inc(x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_4);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_19);
x_52 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_13);
lean_ctor_set(x_52, 2, x_14);
lean_ctor_set(x_52, 3, x_15);
lean_ctor_set(x_52, 4, x_16);
lean_ctor_set(x_52, 5, x_17);
lean_ctor_set(x_52, 6, x_18);
lean_ctor_set(x_52, 7, x_51);
lean_ctor_set(x_52, 8, x_8);
lean_ctor_set(x_52, 9, x_23);
lean_ctor_set_uint8(x_52, sizeof(void*)*10, x_20);
lean_ctor_set_uint8(x_52, sizeof(void*)*10 + 1, x_21);
lean_ctor_set_uint8(x_52, sizeof(void*)*10 + 2, x_22);
x_4 = x_49;
x_5 = x_52;
x_6 = x_35;
goto _start;
}
}
block_60:
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
lean_dec(x_57);
lean_dec(x_33);
lean_dec(x_12);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
else
{
lean_object* x_59; 
lean_dec(x_55);
x_59 = lean_box(0);
x_34 = x_59;
x_35 = x_56;
goto block_54;
}
}
block_104:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Lean_Elab_Term_getCurrMacroScope(x_33, x_61);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_Elab_Term_getEnv___rarg(x_66);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_68, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_68, 3);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 4);
lean_inc(x_74);
x_75 = lean_ctor_get(x_68, 5);
lean_inc(x_75);
x_76 = lean_environment_main_module(x_69);
x_77 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_65);
lean_ctor_set(x_77, 2, x_32);
lean_ctor_set(x_77, 3, x_26);
lean_inc(x_4);
x_78 = l_Lean_Elab_getMacros(x_63, x_4, x_77, x_75);
lean_dec(x_63);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_68);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_68, 5);
lean_dec(x_80);
x_81 = lean_ctor_get(x_68, 4);
lean_dec(x_81);
x_82 = lean_ctor_get(x_68, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_68, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_68, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_68, 0);
lean_dec(x_85);
x_86 = lean_ctor_get(x_78, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_78, 1);
lean_inc(x_87);
lean_dec(x_78);
lean_ctor_set(x_68, 5, x_87);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_86);
x_34 = x_88;
x_35 = x_68;
goto block_54;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_68);
x_89 = lean_ctor_get(x_78, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_78, 1);
lean_inc(x_90);
lean_dec(x_78);
x_91 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_91, 0, x_70);
lean_ctor_set(x_91, 1, x_71);
lean_ctor_set(x_91, 2, x_72);
lean_ctor_set(x_91, 3, x_73);
lean_ctor_set(x_91, 4, x_74);
lean_ctor_set(x_91, 5, x_90);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_89);
x_34 = x_92;
x_35 = x_91;
goto block_54;
}
}
else
{
lean_object* x_93; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
x_93 = lean_ctor_get(x_78, 0);
lean_inc(x_93);
lean_dec(x_78);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
lean_inc(x_33);
x_98 = l_Lean_Elab_Term_throwErrorAt___rarg(x_94, x_97, x_33, x_68);
lean_dec(x_94);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_55 = x_99;
x_56 = x_100;
goto block_60;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_68);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_55 = x_102;
x_56 = x_103;
goto block_60;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_149; lean_object* x_150; lean_object* x_155; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_122 = lean_ctor_get(x_12, 0);
x_123 = lean_ctor_get(x_12, 1);
x_124 = lean_ctor_get(x_12, 2);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_12);
x_125 = lean_nat_add(x_25, x_9);
lean_dec(x_25);
lean_inc(x_26);
lean_inc(x_125);
x_126 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_123);
lean_ctor_set(x_126, 2, x_124);
lean_ctor_set(x_126, 3, x_125);
lean_ctor_set(x_126, 4, x_26);
lean_inc(x_23);
lean_inc(x_8);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_126);
x_127 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_13);
lean_ctor_set(x_127, 2, x_14);
lean_ctor_set(x_127, 3, x_15);
lean_ctor_set(x_127, 4, x_16);
lean_ctor_set(x_127, 5, x_17);
lean_ctor_set(x_127, 6, x_18);
lean_ctor_set(x_127, 7, x_19);
lean_ctor_set(x_127, 8, x_8);
lean_ctor_set(x_127, 9, x_23);
lean_ctor_set_uint8(x_127, sizeof(void*)*10, x_20);
lean_ctor_set_uint8(x_127, sizeof(void*)*10 + 1, x_21);
lean_ctor_set_uint8(x_127, sizeof(void*)*10 + 2, x_22);
x_190 = l_Lean_Elab_Term_getOptions(x_127, x_28);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__2;
x_194 = l_Lean_checkTraceOption(x_191, x_193);
lean_dec(x_191);
if (x_194 == 0)
{
x_155 = x_192;
goto block_189;
}
else
{
lean_object* x_195; 
lean_inc(x_4);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_4);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_196 = l_Lean_Elab_Term_elabTermAux___main___closed__1;
x_197 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
x_198 = l_Lean_Elab_Term_logTrace(x_193, x_197, x_127, x_192);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_155 = x_199;
goto block_189;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_200 = lean_ctor_get(x_1, 0);
lean_inc(x_200);
x_201 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_201, 0, x_200);
x_202 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_203 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_195);
x_205 = l_Lean_Elab_Term_logTrace(x_193, x_204, x_127, x_192);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec(x_205);
x_155 = x_206;
goto block_189;
}
}
block_148:
{
if (lean_obj_tag(x_128) == 0)
{
lean_dec(x_126);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
if (x_3 == 0)
{
lean_object* x_130; 
x_130 = l_Lean_Elab_Term_elabUsingElabFns(x_4, x_1, x_2, x_127, x_129);
return x_130;
}
else
{
lean_object* x_131; 
lean_inc(x_127);
lean_inc(x_1);
lean_inc(x_4);
x_131 = l_Lean_Elab_Term_useImplicitLambda_x3f(x_4, x_1, x_127, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Lean_Elab_Term_elabUsingElabFns(x_4, x_1, x_2, x_127, x_133);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_1);
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
lean_dec(x_131);
x_136 = lean_ctor_get(x_132, 0);
lean_inc(x_136);
lean_dec(x_132);
x_137 = l_Array_empty___closed__1;
x_138 = l_Lean_Elab_Term_elabImplicitLambda___main(x_4, x_2, x_136, x_137, x_127, x_135);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_127);
lean_dec(x_4);
lean_dec(x_1);
x_139 = lean_ctor_get(x_131, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_131, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_141 = x_131;
} else {
 lean_dec_ref(x_131);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_127);
x_143 = lean_ctor_get(x_128, 0);
lean_inc(x_143);
lean_dec(x_128);
lean_inc(x_143);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_4);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_19);
x_146 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_146, 0, x_126);
lean_ctor_set(x_146, 1, x_13);
lean_ctor_set(x_146, 2, x_14);
lean_ctor_set(x_146, 3, x_15);
lean_ctor_set(x_146, 4, x_16);
lean_ctor_set(x_146, 5, x_17);
lean_ctor_set(x_146, 6, x_18);
lean_ctor_set(x_146, 7, x_145);
lean_ctor_set(x_146, 8, x_8);
lean_ctor_set(x_146, 9, x_23);
lean_ctor_set_uint8(x_146, sizeof(void*)*10, x_20);
lean_ctor_set_uint8(x_146, sizeof(void*)*10 + 1, x_21);
lean_ctor_set_uint8(x_146, sizeof(void*)*10 + 2, x_22);
x_4 = x_143;
x_5 = x_146;
x_6 = x_129;
goto _start;
}
}
block_154:
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; 
lean_dec(x_151);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
else
{
lean_object* x_153; 
lean_dec(x_149);
x_153 = lean_box(0);
x_128 = x_153;
x_129 = x_150;
goto block_148;
}
}
block_189:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
lean_dec(x_156);
x_158 = l_Lean_Elab_Term_getCurrMacroScope(x_127, x_155);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l_Lean_Elab_Term_getEnv___rarg(x_160);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_162, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_162, 3);
lean_inc(x_167);
x_168 = lean_ctor_get(x_162, 4);
lean_inc(x_168);
x_169 = lean_ctor_get(x_162, 5);
lean_inc(x_169);
x_170 = lean_environment_main_module(x_163);
x_171 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_159);
lean_ctor_set(x_171, 2, x_125);
lean_ctor_set(x_171, 3, x_26);
lean_inc(x_4);
x_172 = l_Lean_Elab_getMacros(x_157, x_4, x_171, x_169);
lean_dec(x_157);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 lean_ctor_release(x_162, 2);
 lean_ctor_release(x_162, 3);
 lean_ctor_release(x_162, 4);
 lean_ctor_release(x_162, 5);
 x_173 = x_162;
} else {
 lean_dec_ref(x_162);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_dec(x_172);
if (lean_is_scalar(x_173)) {
 x_176 = lean_alloc_ctor(0, 6, 0);
} else {
 x_176 = x_173;
}
lean_ctor_set(x_176, 0, x_164);
lean_ctor_set(x_176, 1, x_165);
lean_ctor_set(x_176, 2, x_166);
lean_ctor_set(x_176, 3, x_167);
lean_ctor_set(x_176, 4, x_168);
lean_ctor_set(x_176, 5, x_175);
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_174);
x_128 = x_177;
x_129 = x_176;
goto block_148;
}
else
{
lean_object* x_178; 
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
x_178 = lean_ctor_get(x_172, 0);
lean_inc(x_178);
lean_dec(x_172);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_181, 0, x_180);
x_182 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_182, 0, x_181);
lean_inc(x_127);
x_183 = l_Lean_Elab_Term_throwErrorAt___rarg(x_179, x_182, x_127, x_162);
lean_dec(x_179);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_149 = x_184;
x_150 = x_185;
goto block_154;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_162);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_149 = x_187;
x_150 = x_188;
goto block_154;
}
}
}
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; uint8_t x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; 
x_214 = lean_ctor_get(x_5, 0);
x_215 = lean_ctor_get(x_5, 1);
x_216 = lean_ctor_get(x_5, 2);
x_217 = lean_ctor_get(x_5, 3);
x_218 = lean_ctor_get(x_5, 4);
x_219 = lean_ctor_get(x_5, 5);
x_220 = lean_ctor_get(x_5, 6);
x_221 = lean_ctor_get(x_5, 7);
x_222 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_223 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_224 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_225 = lean_ctor_get(x_5, 9);
lean_inc(x_225);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_5);
lean_inc(x_225);
lean_inc(x_8);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
x_226 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_226, 0, x_214);
lean_ctor_set(x_226, 1, x_215);
lean_ctor_set(x_226, 2, x_216);
lean_ctor_set(x_226, 3, x_217);
lean_ctor_set(x_226, 4, x_218);
lean_ctor_set(x_226, 5, x_219);
lean_ctor_set(x_226, 6, x_220);
lean_ctor_set(x_226, 7, x_221);
lean_ctor_set(x_226, 8, x_8);
lean_ctor_set(x_226, 9, x_225);
lean_ctor_set_uint8(x_226, sizeof(void*)*10, x_222);
lean_ctor_set_uint8(x_226, sizeof(void*)*10 + 1, x_223);
lean_ctor_set_uint8(x_226, sizeof(void*)*10 + 2, x_224);
x_227 = lean_ctor_get(x_214, 3);
lean_inc(x_227);
x_228 = lean_ctor_get(x_214, 4);
lean_inc(x_228);
x_229 = lean_nat_dec_eq(x_227, x_228);
if (x_229 == 0)
{
lean_dec(x_226);
x_230 = x_6;
goto block_317;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_225);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
x_318 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_319 = l_Lean_Elab_Term_throwError___rarg(x_318, x_226, x_6);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_322 = x_319;
} else {
 lean_dec_ref(x_319);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 2, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_321);
return x_323;
}
block_317:
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_259; lean_object* x_260; lean_object* x_265; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_231 = lean_ctor_get(x_214, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_214, 1);
lean_inc(x_232);
x_233 = lean_ctor_get(x_214, 2);
lean_inc(x_233);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 lean_ctor_release(x_214, 2);
 lean_ctor_release(x_214, 3);
 lean_ctor_release(x_214, 4);
 x_234 = x_214;
} else {
 lean_dec_ref(x_214);
 x_234 = lean_box(0);
}
x_235 = lean_nat_add(x_227, x_9);
lean_dec(x_227);
lean_inc(x_228);
lean_inc(x_235);
if (lean_is_scalar(x_234)) {
 x_236 = lean_alloc_ctor(0, 5, 0);
} else {
 x_236 = x_234;
}
lean_ctor_set(x_236, 0, x_231);
lean_ctor_set(x_236, 1, x_232);
lean_ctor_set(x_236, 2, x_233);
lean_ctor_set(x_236, 3, x_235);
lean_ctor_set(x_236, 4, x_228);
lean_inc(x_225);
lean_inc(x_8);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_236);
x_237 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_215);
lean_ctor_set(x_237, 2, x_216);
lean_ctor_set(x_237, 3, x_217);
lean_ctor_set(x_237, 4, x_218);
lean_ctor_set(x_237, 5, x_219);
lean_ctor_set(x_237, 6, x_220);
lean_ctor_set(x_237, 7, x_221);
lean_ctor_set(x_237, 8, x_8);
lean_ctor_set(x_237, 9, x_225);
lean_ctor_set_uint8(x_237, sizeof(void*)*10, x_222);
lean_ctor_set_uint8(x_237, sizeof(void*)*10 + 1, x_223);
lean_ctor_set_uint8(x_237, sizeof(void*)*10 + 2, x_224);
x_300 = l_Lean_Elab_Term_getOptions(x_237, x_230);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__2;
x_304 = l_Lean_checkTraceOption(x_301, x_303);
lean_dec(x_301);
if (x_304 == 0)
{
x_265 = x_302;
goto block_299;
}
else
{
lean_object* x_305; 
lean_inc(x_4);
x_305 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_305, 0, x_4);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_306 = l_Lean_Elab_Term_elabTermAux___main___closed__1;
x_307 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_305);
x_308 = l_Lean_Elab_Term_logTrace(x_303, x_307, x_237, x_302);
x_309 = lean_ctor_get(x_308, 1);
lean_inc(x_309);
lean_dec(x_308);
x_265 = x_309;
goto block_299;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_310 = lean_ctor_get(x_1, 0);
lean_inc(x_310);
x_311 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_311, 0, x_310);
x_312 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_313 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
x_314 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_305);
x_315 = l_Lean_Elab_Term_logTrace(x_303, x_314, x_237, x_302);
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
lean_dec(x_315);
x_265 = x_316;
goto block_299;
}
}
block_258:
{
if (lean_obj_tag(x_238) == 0)
{
lean_dec(x_236);
lean_dec(x_225);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_8);
if (x_3 == 0)
{
lean_object* x_240; 
x_240 = l_Lean_Elab_Term_elabUsingElabFns(x_4, x_1, x_2, x_237, x_239);
return x_240;
}
else
{
lean_object* x_241; 
lean_inc(x_237);
lean_inc(x_1);
lean_inc(x_4);
x_241 = l_Lean_Elab_Term_useImplicitLambda_x3f(x_4, x_1, x_237, x_239);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = l_Lean_Elab_Term_elabUsingElabFns(x_4, x_1, x_2, x_237, x_243);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_1);
x_245 = lean_ctor_get(x_241, 1);
lean_inc(x_245);
lean_dec(x_241);
x_246 = lean_ctor_get(x_242, 0);
lean_inc(x_246);
lean_dec(x_242);
x_247 = l_Array_empty___closed__1;
x_248 = l_Lean_Elab_Term_elabImplicitLambda___main(x_4, x_2, x_246, x_247, x_237, x_245);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_237);
lean_dec(x_4);
lean_dec(x_1);
x_249 = lean_ctor_get(x_241, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_241, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_251 = x_241;
} else {
 lean_dec_ref(x_241);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_237);
x_253 = lean_ctor_get(x_238, 0);
lean_inc(x_253);
lean_dec(x_238);
lean_inc(x_253);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_4);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_221);
x_256 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_256, 0, x_236);
lean_ctor_set(x_256, 1, x_215);
lean_ctor_set(x_256, 2, x_216);
lean_ctor_set(x_256, 3, x_217);
lean_ctor_set(x_256, 4, x_218);
lean_ctor_set(x_256, 5, x_219);
lean_ctor_set(x_256, 6, x_220);
lean_ctor_set(x_256, 7, x_255);
lean_ctor_set(x_256, 8, x_8);
lean_ctor_set(x_256, 9, x_225);
lean_ctor_set_uint8(x_256, sizeof(void*)*10, x_222);
lean_ctor_set_uint8(x_256, sizeof(void*)*10 + 1, x_223);
lean_ctor_set_uint8(x_256, sizeof(void*)*10 + 2, x_224);
x_4 = x_253;
x_5 = x_256;
x_6 = x_239;
goto _start;
}
}
block_264:
{
lean_object* x_261; 
x_261 = lean_ctor_get(x_259, 0);
lean_inc(x_261);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; 
lean_dec(x_261);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_225);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
else
{
lean_object* x_263; 
lean_dec(x_259);
x_263 = lean_box(0);
x_238 = x_263;
x_239 = x_260;
goto block_258;
}
}
block_299:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
lean_dec(x_266);
x_268 = l_Lean_Elab_Term_getCurrMacroScope(x_237, x_265);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = l_Lean_Elab_Term_getEnv___rarg(x_270);
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 0);
lean_inc(x_273);
lean_dec(x_271);
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_272, 1);
lean_inc(x_275);
x_276 = lean_ctor_get(x_272, 2);
lean_inc(x_276);
x_277 = lean_ctor_get(x_272, 3);
lean_inc(x_277);
x_278 = lean_ctor_get(x_272, 4);
lean_inc(x_278);
x_279 = lean_ctor_get(x_272, 5);
lean_inc(x_279);
x_280 = lean_environment_main_module(x_273);
x_281 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_269);
lean_ctor_set(x_281, 2, x_235);
lean_ctor_set(x_281, 3, x_228);
lean_inc(x_4);
x_282 = l_Lean_Elab_getMacros(x_267, x_4, x_281, x_279);
lean_dec(x_267);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 lean_ctor_release(x_272, 3);
 lean_ctor_release(x_272, 4);
 lean_ctor_release(x_272, 5);
 x_283 = x_272;
} else {
 lean_dec_ref(x_272);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_282, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_282, 1);
lean_inc(x_285);
lean_dec(x_282);
if (lean_is_scalar(x_283)) {
 x_286 = lean_alloc_ctor(0, 6, 0);
} else {
 x_286 = x_283;
}
lean_ctor_set(x_286, 0, x_274);
lean_ctor_set(x_286, 1, x_275);
lean_ctor_set(x_286, 2, x_276);
lean_ctor_set(x_286, 3, x_277);
lean_ctor_set(x_286, 4, x_278);
lean_ctor_set(x_286, 5, x_285);
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_284);
x_238 = x_287;
x_239 = x_286;
goto block_258;
}
else
{
lean_object* x_288; 
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
x_288 = lean_ctor_get(x_282, 0);
lean_inc(x_288);
lean_dec(x_282);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
x_291 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_291, 0, x_290);
x_292 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_292, 0, x_291);
lean_inc(x_237);
x_293 = l_Lean_Elab_Term_throwErrorAt___rarg(x_289, x_292, x_237, x_272);
lean_dec(x_289);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
x_259 = x_294;
x_260 = x_295;
goto block_264;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_272);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_259 = x_297;
x_260 = x_298;
goto block_264;
}
}
}
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; uint8_t x_342; uint8_t x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; lean_object* x_350; 
x_324 = lean_ctor_get(x_6, 0);
x_325 = lean_ctor_get(x_6, 1);
x_326 = lean_ctor_get(x_6, 2);
x_327 = lean_ctor_get(x_6, 3);
x_328 = lean_ctor_get(x_6, 4);
x_329 = lean_ctor_get(x_6, 5);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_6);
x_330 = lean_unsigned_to_nat(1u);
x_331 = lean_nat_add(x_329, x_330);
x_332 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_332, 0, x_324);
lean_ctor_set(x_332, 1, x_325);
lean_ctor_set(x_332, 2, x_326);
lean_ctor_set(x_332, 3, x_327);
lean_ctor_set(x_332, 4, x_328);
lean_ctor_set(x_332, 5, x_331);
x_333 = lean_ctor_get(x_5, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_5, 1);
lean_inc(x_334);
x_335 = lean_ctor_get(x_5, 2);
lean_inc(x_335);
x_336 = lean_ctor_get(x_5, 3);
lean_inc(x_336);
x_337 = lean_ctor_get(x_5, 4);
lean_inc(x_337);
x_338 = lean_ctor_get(x_5, 5);
lean_inc(x_338);
x_339 = lean_ctor_get(x_5, 6);
lean_inc(x_339);
x_340 = lean_ctor_get(x_5, 7);
lean_inc(x_340);
x_341 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_342 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_343 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_344 = lean_ctor_get(x_5, 9);
lean_inc(x_344);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 lean_ctor_release(x_5, 8);
 lean_ctor_release(x_5, 9);
 x_345 = x_5;
} else {
 lean_dec_ref(x_5);
 x_345 = lean_box(0);
}
lean_inc(x_344);
lean_inc(x_329);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
if (lean_is_scalar(x_345)) {
 x_346 = lean_alloc_ctor(0, 10, 3);
} else {
 x_346 = x_345;
}
lean_ctor_set(x_346, 0, x_333);
lean_ctor_set(x_346, 1, x_334);
lean_ctor_set(x_346, 2, x_335);
lean_ctor_set(x_346, 3, x_336);
lean_ctor_set(x_346, 4, x_337);
lean_ctor_set(x_346, 5, x_338);
lean_ctor_set(x_346, 6, x_339);
lean_ctor_set(x_346, 7, x_340);
lean_ctor_set(x_346, 8, x_329);
lean_ctor_set(x_346, 9, x_344);
lean_ctor_set_uint8(x_346, sizeof(void*)*10, x_341);
lean_ctor_set_uint8(x_346, sizeof(void*)*10 + 1, x_342);
lean_ctor_set_uint8(x_346, sizeof(void*)*10 + 2, x_343);
x_347 = lean_ctor_get(x_333, 3);
lean_inc(x_347);
x_348 = lean_ctor_get(x_333, 4);
lean_inc(x_348);
x_349 = lean_nat_dec_eq(x_347, x_348);
if (x_349 == 0)
{
lean_dec(x_346);
x_350 = x_332;
goto block_437;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_344);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_329);
lean_dec(x_4);
lean_dec(x_1);
x_438 = l_Lean_Meta_withIncRecDepth___rarg___closed__2;
x_439 = l_Lean_Elab_Term_throwError___rarg(x_438, x_346, x_332);
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_442 = x_439;
} else {
 lean_dec_ref(x_439);
 x_442 = lean_box(0);
}
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(1, 2, 0);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_440);
lean_ctor_set(x_443, 1, x_441);
return x_443;
}
block_437:
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_379; lean_object* x_380; lean_object* x_385; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; 
x_351 = lean_ctor_get(x_333, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_333, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_333, 2);
lean_inc(x_353);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 lean_ctor_release(x_333, 2);
 lean_ctor_release(x_333, 3);
 lean_ctor_release(x_333, 4);
 x_354 = x_333;
} else {
 lean_dec_ref(x_333);
 x_354 = lean_box(0);
}
x_355 = lean_nat_add(x_347, x_330);
lean_dec(x_347);
lean_inc(x_348);
lean_inc(x_355);
if (lean_is_scalar(x_354)) {
 x_356 = lean_alloc_ctor(0, 5, 0);
} else {
 x_356 = x_354;
}
lean_ctor_set(x_356, 0, x_351);
lean_ctor_set(x_356, 1, x_352);
lean_ctor_set(x_356, 2, x_353);
lean_ctor_set(x_356, 3, x_355);
lean_ctor_set(x_356, 4, x_348);
lean_inc(x_344);
lean_inc(x_329);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_356);
x_357 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_334);
lean_ctor_set(x_357, 2, x_335);
lean_ctor_set(x_357, 3, x_336);
lean_ctor_set(x_357, 4, x_337);
lean_ctor_set(x_357, 5, x_338);
lean_ctor_set(x_357, 6, x_339);
lean_ctor_set(x_357, 7, x_340);
lean_ctor_set(x_357, 8, x_329);
lean_ctor_set(x_357, 9, x_344);
lean_ctor_set_uint8(x_357, sizeof(void*)*10, x_341);
lean_ctor_set_uint8(x_357, sizeof(void*)*10 + 1, x_342);
lean_ctor_set_uint8(x_357, sizeof(void*)*10 + 2, x_343);
x_420 = l_Lean_Elab_Term_getOptions(x_357, x_350);
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__2;
x_424 = l_Lean_checkTraceOption(x_421, x_423);
lean_dec(x_421);
if (x_424 == 0)
{
x_385 = x_422;
goto block_419;
}
else
{
lean_object* x_425; 
lean_inc(x_4);
x_425 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_425, 0, x_4);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_426 = l_Lean_Elab_Term_elabTermAux___main___closed__1;
x_427 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_425);
x_428 = l_Lean_Elab_Term_logTrace(x_423, x_427, x_357, x_422);
x_429 = lean_ctor_get(x_428, 1);
lean_inc(x_429);
lean_dec(x_428);
x_385 = x_429;
goto block_419;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_430 = lean_ctor_get(x_1, 0);
lean_inc(x_430);
x_431 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_431, 0, x_430);
x_432 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_433 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
x_434 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_425);
x_435 = l_Lean_Elab_Term_logTrace(x_423, x_434, x_357, x_422);
x_436 = lean_ctor_get(x_435, 1);
lean_inc(x_436);
lean_dec(x_435);
x_385 = x_436;
goto block_419;
}
}
block_378:
{
if (lean_obj_tag(x_358) == 0)
{
lean_dec(x_356);
lean_dec(x_344);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_329);
if (x_3 == 0)
{
lean_object* x_360; 
x_360 = l_Lean_Elab_Term_elabUsingElabFns(x_4, x_1, x_2, x_357, x_359);
return x_360;
}
else
{
lean_object* x_361; 
lean_inc(x_357);
lean_inc(x_1);
lean_inc(x_4);
x_361 = l_Lean_Elab_Term_useImplicitLambda_x3f(x_4, x_1, x_357, x_359);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; 
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec(x_361);
x_364 = l_Lean_Elab_Term_elabUsingElabFns(x_4, x_1, x_2, x_357, x_363);
return x_364;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_dec(x_1);
x_365 = lean_ctor_get(x_361, 1);
lean_inc(x_365);
lean_dec(x_361);
x_366 = lean_ctor_get(x_362, 0);
lean_inc(x_366);
lean_dec(x_362);
x_367 = l_Array_empty___closed__1;
x_368 = l_Lean_Elab_Term_elabImplicitLambda___main(x_4, x_2, x_366, x_367, x_357, x_365);
return x_368;
}
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_357);
lean_dec(x_4);
lean_dec(x_1);
x_369 = lean_ctor_get(x_361, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_361, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_371 = x_361;
} else {
 lean_dec_ref(x_361);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(1, 2, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_369);
lean_ctor_set(x_372, 1, x_370);
return x_372;
}
}
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_357);
x_373 = lean_ctor_get(x_358, 0);
lean_inc(x_373);
lean_dec(x_358);
lean_inc(x_373);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_4);
lean_ctor_set(x_374, 1, x_373);
x_375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_340);
x_376 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_376, 0, x_356);
lean_ctor_set(x_376, 1, x_334);
lean_ctor_set(x_376, 2, x_335);
lean_ctor_set(x_376, 3, x_336);
lean_ctor_set(x_376, 4, x_337);
lean_ctor_set(x_376, 5, x_338);
lean_ctor_set(x_376, 6, x_339);
lean_ctor_set(x_376, 7, x_375);
lean_ctor_set(x_376, 8, x_329);
lean_ctor_set(x_376, 9, x_344);
lean_ctor_set_uint8(x_376, sizeof(void*)*10, x_341);
lean_ctor_set_uint8(x_376, sizeof(void*)*10 + 1, x_342);
lean_ctor_set_uint8(x_376, sizeof(void*)*10 + 2, x_343);
x_4 = x_373;
x_5 = x_376;
x_6 = x_359;
goto _start;
}
}
block_384:
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_379, 0);
lean_inc(x_381);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; 
lean_dec(x_381);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_344);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_329);
lean_dec(x_4);
lean_dec(x_1);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_379);
lean_ctor_set(x_382, 1, x_380);
return x_382;
}
else
{
lean_object* x_383; 
lean_dec(x_379);
x_383 = lean_box(0);
x_358 = x_383;
x_359 = x_380;
goto block_378;
}
}
block_419:
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
lean_dec(x_386);
x_388 = l_Lean_Elab_Term_getCurrMacroScope(x_357, x_385);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = l_Lean_Elab_Term_getEnv___rarg(x_390);
x_392 = lean_ctor_get(x_391, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 0);
lean_inc(x_393);
lean_dec(x_391);
x_394 = lean_ctor_get(x_392, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_392, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_392, 2);
lean_inc(x_396);
x_397 = lean_ctor_get(x_392, 3);
lean_inc(x_397);
x_398 = lean_ctor_get(x_392, 4);
lean_inc(x_398);
x_399 = lean_ctor_get(x_392, 5);
lean_inc(x_399);
x_400 = lean_environment_main_module(x_393);
x_401 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_389);
lean_ctor_set(x_401, 2, x_355);
lean_ctor_set(x_401, 3, x_348);
lean_inc(x_4);
x_402 = l_Lean_Elab_getMacros(x_387, x_4, x_401, x_399);
lean_dec(x_387);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 lean_ctor_release(x_392, 2);
 lean_ctor_release(x_392, 3);
 lean_ctor_release(x_392, 4);
 lean_ctor_release(x_392, 5);
 x_403 = x_392;
} else {
 lean_dec_ref(x_392);
 x_403 = lean_box(0);
}
x_404 = lean_ctor_get(x_402, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_402, 1);
lean_inc(x_405);
lean_dec(x_402);
if (lean_is_scalar(x_403)) {
 x_406 = lean_alloc_ctor(0, 6, 0);
} else {
 x_406 = x_403;
}
lean_ctor_set(x_406, 0, x_394);
lean_ctor_set(x_406, 1, x_395);
lean_ctor_set(x_406, 2, x_396);
lean_ctor_set(x_406, 3, x_397);
lean_ctor_set(x_406, 4, x_398);
lean_ctor_set(x_406, 5, x_405);
x_407 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_407, 0, x_404);
x_358 = x_407;
x_359 = x_406;
goto block_378;
}
else
{
lean_object* x_408; 
lean_dec(x_398);
lean_dec(x_397);
lean_dec(x_396);
lean_dec(x_395);
lean_dec(x_394);
x_408 = lean_ctor_get(x_402, 0);
lean_inc(x_408);
lean_dec(x_402);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
x_411 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_411, 0, x_410);
x_412 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_412, 0, x_411);
lean_inc(x_357);
x_413 = l_Lean_Elab_Term_throwErrorAt___rarg(x_409, x_412, x_357, x_392);
lean_dec(x_409);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec(x_413);
x_379 = x_414;
x_380 = x_415;
goto block_384;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_416 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_392);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec(x_416);
x_379 = x_417;
x_380 = x_418;
goto block_384;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_elabTermAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Lean_Elab_Term_elabTermAux___main(x_1, x_7, x_8, x_4, x_5, x_6);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_elabTermAux(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_elabTermAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabTermAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Lean_Elab_Term_elabTermAux(x_1, x_7, x_8, x_4, x_5, x_6);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_elabTerm(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 9);
x_8 = l_Lean_Elab_replaceRef(x_1, x_7);
lean_dec(x_7);
lean_ctor_set(x_4, 9, x_8);
x_9 = 1;
x_10 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_3, x_9, x_1, x_4, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 4);
x_16 = lean_ctor_get(x_4, 5);
x_17 = lean_ctor_get(x_4, 6);
x_18 = lean_ctor_get(x_4, 7);
x_19 = lean_ctor_get(x_4, 8);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_22 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_23 = lean_ctor_get(x_4, 9);
lean_inc(x_23);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_24 = l_Lean_Elab_replaceRef(x_1, x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_25, 2, x_13);
lean_ctor_set(x_25, 3, x_14);
lean_ctor_set(x_25, 4, x_15);
lean_ctor_set(x_25, 5, x_16);
lean_ctor_set(x_25, 6, x_17);
lean_ctor_set(x_25, 7, x_18);
lean_ctor_set(x_25, 8, x_19);
lean_ctor_set(x_25, 9, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*10, x_20);
lean_ctor_set_uint8(x_25, sizeof(void*)*10 + 1, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*10 + 2, x_22);
x_26 = 1;
x_27 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_3, x_26, x_1, x_25, x_5);
return x_27;
}
}
}
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabTermWithoutImplicitLambdas(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_3, x_6, x_1, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabTermWithoutImplicitLambdas___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_Term_elabTermWithoutImplicitLambdas(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_adaptExpander(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_2);
x_6 = lean_apply_3(x_1, x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_4, 7);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_7);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_4, 7, x_12);
x_13 = 1;
x_14 = l_Lean_Elab_Term_elabTerm(x_7, x_3, x_13, x_4, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_4, 2);
x_18 = lean_ctor_get(x_4, 3);
x_19 = lean_ctor_get(x_4, 4);
x_20 = lean_ctor_get(x_4, 5);
x_21 = lean_ctor_get(x_4, 6);
x_22 = lean_ctor_get(x_4, 7);
x_23 = lean_ctor_get(x_4, 8);
x_24 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_25 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_26 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_27 = lean_ctor_get(x_4, 9);
lean_inc(x_27);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
lean_inc(x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_7);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
x_30 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set(x_30, 1, x_16);
lean_ctor_set(x_30, 2, x_17);
lean_ctor_set(x_30, 3, x_18);
lean_ctor_set(x_30, 4, x_19);
lean_ctor_set(x_30, 5, x_20);
lean_ctor_set(x_30, 6, x_21);
lean_ctor_set(x_30, 7, x_29);
lean_ctor_set(x_30, 8, x_23);
lean_ctor_set(x_30, 9, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*10, x_24);
lean_ctor_set_uint8(x_30, sizeof(void*)*10 + 1, x_25);
lean_ctor_set_uint8(x_30, sizeof(void*)*10 + 2, x_26);
x_31 = 1;
x_32 = l_Lean_Elab_Term_elabTerm(x_7, x_3, x_31, x_30, x_8);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
lean_object* l_Lean_Elab_Term_withLCtx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_dec(x_10);
lean_ctor_set(x_7, 2, x_2);
lean_ctor_set(x_7, 1, x_1);
x_11 = lean_apply_2(x_3, x_4, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 3);
x_14 = lean_ctor_get(x_7, 4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_1);
lean_ctor_set(x_15, 2, x_2);
lean_ctor_set(x_15, 3, x_13);
lean_ctor_set(x_15, 4, x_14);
lean_ctor_set(x_4, 0, x_15);
x_16 = lean_apply_2(x_3, x_4, x_5);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_ctor_get(x_4, 3);
x_21 = lean_ctor_get(x_4, 4);
x_22 = lean_ctor_get(x_4, 5);
x_23 = lean_ctor_get(x_4, 6);
x_24 = lean_ctor_get(x_4, 7);
x_25 = lean_ctor_get(x_4, 8);
x_26 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_27 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_28 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_29 = lean_ctor_get(x_4, 9);
lean_inc(x_29);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_30 = lean_ctor_get(x_17, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_17, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_17, 4);
lean_inc(x_32);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 x_33 = x_17;
} else {
 lean_dec_ref(x_17);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 5, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_1);
lean_ctor_set(x_34, 2, x_2);
lean_ctor_set(x_34, 3, x_31);
lean_ctor_set(x_34, 4, x_32);
x_35 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_18);
lean_ctor_set(x_35, 2, x_19);
lean_ctor_set(x_35, 3, x_20);
lean_ctor_set(x_35, 4, x_21);
lean_ctor_set(x_35, 5, x_22);
lean_ctor_set(x_35, 6, x_23);
lean_ctor_set(x_35, 7, x_24);
lean_ctor_set(x_35, 8, x_25);
lean_ctor_set(x_35, 9, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*10, x_26);
lean_ctor_set_uint8(x_35, sizeof(void*)*10 + 1, x_27);
lean_ctor_set_uint8(x_35, sizeof(void*)*10 + 2, x_28);
x_36 = lean_apply_2(x_3, x_35, x_5);
return x_36;
}
}
}
lean_object* l_Lean_Elab_Term_withLCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withLCtx___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_dec(x_5);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 2);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 2);
lean_dec(x_9);
x_10 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_3, 2, x_10);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 3);
x_16 = lean_ctor_get(x_3, 4);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_17 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_16);
lean_ctor_set(x_2, 2, x_18);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_1);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 3);
x_24 = lean_ctor_get(x_2, 4);
x_25 = lean_ctor_get(x_2, 5);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 4);
lean_inc(x_29);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_30 = x_3;
} else {
 lean_dec_ref(x_3);
 x_30 = lean_box(0);
}
x_31 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 5, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set(x_32, 3, x_28);
lean_ctor_set(x_32, 4, x_29);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_22);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set(x_33, 4, x_24);
lean_ctor_set(x_33, 5, x_25);
lean_ctor_set(x_1, 0, x_33);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_1);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = lean_ctor_get(x_1, 4);
x_40 = lean_ctor_get(x_1, 5);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_1);
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_2, 5);
lean_inc(x_45);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_46 = x_2;
} else {
 lean_dec_ref(x_2);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_3, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_3, 3);
lean_inc(x_49);
x_50 = lean_ctor_get(x_3, 4);
lean_inc(x_50);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_51 = x_3;
} else {
 lean_dec_ref(x_3);
 x_51 = lean_box(0);
}
x_52 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 5, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_52);
lean_ctor_set(x_53, 3, x_49);
lean_ctor_set(x_53, 4, x_50);
if (lean_is_scalar(x_46)) {
 x_54 = lean_alloc_ctor(0, 6, 0);
} else {
 x_54 = x_46;
}
lean_ctor_set(x_54, 0, x_41);
lean_ctor_set(x_54, 1, x_42);
lean_ctor_set(x_54, 2, x_53);
lean_ctor_set(x_54, 3, x_43);
lean_ctor_set(x_54, 4, x_44);
lean_ctor_set(x_54, 5, x_45);
x_55 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_36);
lean_ctor_set(x_55, 2, x_37);
lean_ctor_set(x_55, 3, x_38);
lean_ctor_set(x_55, 4, x_39);
lean_ctor_set(x_55, 5, x_40);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_resetSynthInstanceCache___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_resetSynthInstanceCache(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_108 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_3);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_apply_2(x_1, x_2, x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_111);
x_7 = x_113;
x_8 = x_112;
goto block_107;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_110, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_114);
x_7 = x_116;
x_8 = x_115;
goto block_107;
}
block_107:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_9, 2);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 2);
lean_dec(x_17);
lean_ctor_set(x_10, 2, x_6);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
x_21 = lean_ctor_get(x_10, 3);
x_22 = lean_ctor_get(x_10, 4);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_6);
lean_ctor_set(x_23, 3, x_21);
lean_ctor_set(x_23, 4, x_22);
lean_ctor_set(x_9, 2, x_23);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_8);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_9, 0);
x_26 = lean_ctor_get(x_9, 1);
x_27 = lean_ctor_get(x_9, 3);
x_28 = lean_ctor_get(x_9, 4);
x_29 = lean_ctor_get(x_9, 5);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_9);
x_30 = lean_ctor_get(x_10, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_10, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_10, 4);
lean_inc(x_33);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 lean_ctor_release(x_10, 4);
 x_34 = x_10;
} else {
 lean_dec_ref(x_10);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 5, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_6);
lean_ctor_set(x_35, 3, x_32);
lean_ctor_set(x_35, 4, x_33);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_25);
lean_ctor_set(x_36, 1, x_26);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_27);
lean_ctor_set(x_36, 4, x_28);
lean_ctor_set(x_36, 5, x_29);
lean_ctor_set(x_8, 0, x_36);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_11);
lean_ctor_set(x_37, 1, x_8);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_38 = lean_ctor_get(x_8, 1);
x_39 = lean_ctor_get(x_8, 2);
x_40 = lean_ctor_get(x_8, 3);
x_41 = lean_ctor_get(x_8, 4);
x_42 = lean_ctor_get(x_8, 5);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_8);
x_43 = lean_ctor_get(x_9, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_9, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_9, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_9, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_9, 5);
lean_inc(x_47);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 lean_ctor_release(x_9, 4);
 lean_ctor_release(x_9, 5);
 x_48 = x_9;
} else {
 lean_dec_ref(x_9);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_10, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_10, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_10, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_10, 4);
lean_inc(x_52);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 lean_ctor_release(x_10, 4);
 x_53 = x_10;
} else {
 lean_dec_ref(x_10);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 5, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_6);
lean_ctor_set(x_54, 3, x_51);
lean_ctor_set(x_54, 4, x_52);
if (lean_is_scalar(x_48)) {
 x_55 = lean_alloc_ctor(0, 6, 0);
} else {
 x_55 = x_48;
}
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_44);
lean_ctor_set(x_55, 2, x_54);
lean_ctor_set(x_55, 3, x_45);
lean_ctor_set(x_55, 4, x_46);
lean_ctor_set(x_55, 5, x_47);
x_56 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_38);
lean_ctor_set(x_56, 2, x_39);
lean_ctor_set(x_56, 3, x_40);
lean_ctor_set(x_56, 4, x_41);
lean_ctor_set(x_56, 5, x_42);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_11);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_8, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_7, 0);
lean_inc(x_60);
lean_dec(x_7);
x_61 = !lean_is_exclusive(x_8);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_8, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_58);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_58, 2);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_59);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_59, 2);
lean_dec(x_66);
lean_ctor_set(x_59, 2, x_6);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_8);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_59, 0);
x_69 = lean_ctor_get(x_59, 1);
x_70 = lean_ctor_get(x_59, 3);
x_71 = lean_ctor_get(x_59, 4);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_59);
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_69);
lean_ctor_set(x_72, 2, x_6);
lean_ctor_set(x_72, 3, x_70);
lean_ctor_set(x_72, 4, x_71);
lean_ctor_set(x_58, 2, x_72);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_60);
lean_ctor_set(x_73, 1, x_8);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_74 = lean_ctor_get(x_58, 0);
x_75 = lean_ctor_get(x_58, 1);
x_76 = lean_ctor_get(x_58, 3);
x_77 = lean_ctor_get(x_58, 4);
x_78 = lean_ctor_get(x_58, 5);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_58);
x_79 = lean_ctor_get(x_59, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_59, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_59, 3);
lean_inc(x_81);
x_82 = lean_ctor_get(x_59, 4);
lean_inc(x_82);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 lean_ctor_release(x_59, 4);
 x_83 = x_59;
} else {
 lean_dec_ref(x_59);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 5, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_80);
lean_ctor_set(x_84, 2, x_6);
lean_ctor_set(x_84, 3, x_81);
lean_ctor_set(x_84, 4, x_82);
x_85 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_85, 0, x_74);
lean_ctor_set(x_85, 1, x_75);
lean_ctor_set(x_85, 2, x_84);
lean_ctor_set(x_85, 3, x_76);
lean_ctor_set(x_85, 4, x_77);
lean_ctor_set(x_85, 5, x_78);
lean_ctor_set(x_8, 0, x_85);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_60);
lean_ctor_set(x_86, 1, x_8);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_87 = lean_ctor_get(x_8, 1);
x_88 = lean_ctor_get(x_8, 2);
x_89 = lean_ctor_get(x_8, 3);
x_90 = lean_ctor_get(x_8, 4);
x_91 = lean_ctor_get(x_8, 5);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_8);
x_92 = lean_ctor_get(x_58, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_58, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_58, 3);
lean_inc(x_94);
x_95 = lean_ctor_get(x_58, 4);
lean_inc(x_95);
x_96 = lean_ctor_get(x_58, 5);
lean_inc(x_96);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 lean_ctor_release(x_58, 4);
 lean_ctor_release(x_58, 5);
 x_97 = x_58;
} else {
 lean_dec_ref(x_58);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_59, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_59, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_59, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_59, 4);
lean_inc(x_101);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 lean_ctor_release(x_59, 4);
 x_102 = x_59;
} else {
 lean_dec_ref(x_59);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 5, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_99);
lean_ctor_set(x_103, 2, x_6);
lean_ctor_set(x_103, 3, x_100);
lean_ctor_set(x_103, 4, x_101);
if (lean_is_scalar(x_97)) {
 x_104 = lean_alloc_ctor(0, 6, 0);
} else {
 x_104 = x_97;
}
lean_ctor_set(x_104, 0, x_92);
lean_ctor_set(x_104, 1, x_93);
lean_ctor_set(x_104, 2, x_103);
lean_ctor_set(x_104, 3, x_94);
lean_ctor_set(x_104, 4, x_95);
lean_ctor_set(x_104, 5, x_96);
x_105 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_87);
lean_ctor_set(x_105, 2, x_88);
lean_ctor_set(x_105, 3, x_89);
lean_ctor_set(x_105, 4, x_90);
lean_ctor_set(x_105, 5, x_91);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_60);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_resettingSynthInstanceCache___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCacheWhen___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_1 == 0)
{
lean_object* x_5; 
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_110 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_4);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_apply_2(x_2, x_3, x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_113);
x_9 = x_115;
x_10 = x_114;
goto block_109;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_112, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
lean_dec(x_112);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_116);
x_9 = x_118;
x_10 = x_117;
goto block_109;
}
block_109:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_11, 2);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_12, 2);
lean_dec(x_19);
lean_ctor_set(x_12, 2, x_8);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
x_23 = lean_ctor_get(x_12, 3);
x_24 = lean_ctor_get(x_12, 4);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_8);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set(x_11, 2, x_25);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_13);
lean_ctor_set(x_26, 1, x_10);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
x_29 = lean_ctor_get(x_11, 3);
x_30 = lean_ctor_get(x_11, 4);
x_31 = lean_ctor_get(x_11, 5);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_32 = lean_ctor_get(x_12, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_12, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_12, 4);
lean_inc(x_35);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_36 = x_12;
} else {
 lean_dec_ref(x_12);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 5, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_8);
lean_ctor_set(x_37, 3, x_34);
lean_ctor_set(x_37, 4, x_35);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_28);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_38, 3, x_29);
lean_ctor_set(x_38, 4, x_30);
lean_ctor_set(x_38, 5, x_31);
lean_ctor_set(x_10, 0, x_38);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_13);
lean_ctor_set(x_39, 1, x_10);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_40 = lean_ctor_get(x_10, 1);
x_41 = lean_ctor_get(x_10, 2);
x_42 = lean_ctor_get(x_10, 3);
x_43 = lean_ctor_get(x_10, 4);
x_44 = lean_ctor_get(x_10, 5);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_10);
x_45 = lean_ctor_get(x_11, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_11, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_11, 4);
lean_inc(x_48);
x_49 = lean_ctor_get(x_11, 5);
lean_inc(x_49);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 x_50 = x_11;
} else {
 lean_dec_ref(x_11);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_12, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_12, 3);
lean_inc(x_53);
x_54 = lean_ctor_get(x_12, 4);
lean_inc(x_54);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_55 = x_12;
} else {
 lean_dec_ref(x_12);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 5, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_52);
lean_ctor_set(x_56, 2, x_8);
lean_ctor_set(x_56, 3, x_53);
lean_ctor_set(x_56, 4, x_54);
if (lean_is_scalar(x_50)) {
 x_57 = lean_alloc_ctor(0, 6, 0);
} else {
 x_57 = x_50;
}
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_46);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_47);
lean_ctor_set(x_57, 4, x_48);
lean_ctor_set(x_57, 5, x_49);
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_40);
lean_ctor_set(x_58, 2, x_41);
lean_ctor_set(x_58, 3, x_42);
lean_ctor_set(x_58, 4, x_43);
lean_ctor_set(x_58, 5, x_44);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_13);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_10, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_9, 0);
lean_inc(x_62);
lean_dec(x_9);
x_63 = !lean_is_exclusive(x_10);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_10, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_60, 2);
lean_dec(x_66);
x_67 = !lean_is_exclusive(x_61);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_61, 2);
lean_dec(x_68);
lean_ctor_set(x_61, 2, x_8);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_10);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_61, 0);
x_71 = lean_ctor_get(x_61, 1);
x_72 = lean_ctor_get(x_61, 3);
x_73 = lean_ctor_get(x_61, 4);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_61);
x_74 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_71);
lean_ctor_set(x_74, 2, x_8);
lean_ctor_set(x_74, 3, x_72);
lean_ctor_set(x_74, 4, x_73);
lean_ctor_set(x_60, 2, x_74);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_62);
lean_ctor_set(x_75, 1, x_10);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_76 = lean_ctor_get(x_60, 0);
x_77 = lean_ctor_get(x_60, 1);
x_78 = lean_ctor_get(x_60, 3);
x_79 = lean_ctor_get(x_60, 4);
x_80 = lean_ctor_get(x_60, 5);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_60);
x_81 = lean_ctor_get(x_61, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_61, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_61, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_61, 4);
lean_inc(x_84);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 lean_ctor_release(x_61, 3);
 lean_ctor_release(x_61, 4);
 x_85 = x_61;
} else {
 lean_dec_ref(x_61);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 5, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_82);
lean_ctor_set(x_86, 2, x_8);
lean_ctor_set(x_86, 3, x_83);
lean_ctor_set(x_86, 4, x_84);
x_87 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_87, 0, x_76);
lean_ctor_set(x_87, 1, x_77);
lean_ctor_set(x_87, 2, x_86);
lean_ctor_set(x_87, 3, x_78);
lean_ctor_set(x_87, 4, x_79);
lean_ctor_set(x_87, 5, x_80);
lean_ctor_set(x_10, 0, x_87);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_62);
lean_ctor_set(x_88, 1, x_10);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_89 = lean_ctor_get(x_10, 1);
x_90 = lean_ctor_get(x_10, 2);
x_91 = lean_ctor_get(x_10, 3);
x_92 = lean_ctor_get(x_10, 4);
x_93 = lean_ctor_get(x_10, 5);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_10);
x_94 = lean_ctor_get(x_60, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_60, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_60, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_60, 4);
lean_inc(x_97);
x_98 = lean_ctor_get(x_60, 5);
lean_inc(x_98);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 lean_ctor_release(x_60, 2);
 lean_ctor_release(x_60, 3);
 lean_ctor_release(x_60, 4);
 lean_ctor_release(x_60, 5);
 x_99 = x_60;
} else {
 lean_dec_ref(x_60);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_61, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_61, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_61, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_61, 4);
lean_inc(x_103);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 lean_ctor_release(x_61, 3);
 lean_ctor_release(x_61, 4);
 x_104 = x_61;
} else {
 lean_dec_ref(x_61);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 5, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_100);
lean_ctor_set(x_105, 1, x_101);
lean_ctor_set(x_105, 2, x_8);
lean_ctor_set(x_105, 3, x_102);
lean_ctor_set(x_105, 4, x_103);
if (lean_is_scalar(x_99)) {
 x_106 = lean_alloc_ctor(0, 6, 0);
} else {
 x_106 = x_99;
}
lean_ctor_set(x_106, 0, x_94);
lean_ctor_set(x_106, 1, x_95);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set(x_106, 3, x_96);
lean_ctor_set(x_106, 4, x_97);
lean_ctor_set(x_106, 5, x_98);
x_107 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_89);
lean_ctor_set(x_107, 2, x_90);
lean_ctor_set(x_107, 3, x_91);
lean_ctor_set(x_107, 4, x_92);
lean_ctor_set(x_107, 5, x_93);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_62);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCacheWhen(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_resettingSynthInstanceCacheWhen___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCacheWhen___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Elab_Term_resettingSynthInstanceCacheWhen___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_Elab_Term_withLocalContext___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_LocalInstance_beq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Term_withLocalContext___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_6 = l_Lean_Elab_Term_getLocalInsts(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_10 = lean_array_get_size(x_2);
x_11 = lean_array_get_size(x_7);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 2);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_dec(x_17);
lean_inc(x_2);
lean_ctor_set(x_14, 2, x_2);
lean_ctor_set(x_14, 1, x_1);
if (x_12 == 0)
{
lean_object* x_133; 
lean_dec(x_7);
lean_dec(x_2);
x_133 = lean_box(0);
x_18 = x_133;
goto block_132;
}
else
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_unsigned_to_nat(0u);
x_135 = l_Array_isEqvAux___main___at_Lean_Elab_Term_withLocalContext___spec__1(x_2, x_7, lean_box(0), x_2, x_7, x_134);
lean_dec(x_7);
lean_dec(x_2);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_box(0);
x_18 = x_136;
goto block_132;
}
else
{
lean_object* x_137; 
lean_dec(x_9);
x_137 = lean_apply_2(x_3, x_4, x_8);
return x_137;
}
}
block_132:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_18);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
lean_dec(x_20);
x_123 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_8);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_125 = lean_apply_2(x_3, x_4, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_126);
x_22 = x_128;
x_23 = x_127;
goto block_122;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_125, 1);
lean_inc(x_130);
lean_dec(x_125);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_129);
x_22 = x_131;
x_23 = x_130;
goto block_122;
}
block_122:
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_23, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_24, 2);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_25, 2);
lean_dec(x_32);
lean_ctor_set(x_25, 2, x_21);
if (lean_is_scalar(x_9)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_9;
 lean_ctor_set_tag(x_33, 1);
}
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_23);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
x_36 = lean_ctor_get(x_25, 3);
x_37 = lean_ctor_get(x_25, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_35);
lean_ctor_set(x_38, 2, x_21);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 4, x_37);
lean_ctor_set(x_24, 2, x_38);
if (lean_is_scalar(x_9)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_9;
 lean_ctor_set_tag(x_39, 1);
}
lean_ctor_set(x_39, 0, x_26);
lean_ctor_set(x_39, 1, x_23);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
x_42 = lean_ctor_get(x_24, 3);
x_43 = lean_ctor_get(x_24, 4);
x_44 = lean_ctor_get(x_24, 5);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_45 = lean_ctor_get(x_25, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_25, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_25, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_25, 4);
lean_inc(x_48);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 lean_ctor_release(x_25, 4);
 x_49 = x_25;
} else {
 lean_dec_ref(x_25);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 5, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_50, 2, x_21);
lean_ctor_set(x_50, 3, x_47);
lean_ctor_set(x_50, 4, x_48);
x_51 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_51, 0, x_40);
lean_ctor_set(x_51, 1, x_41);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_51, 3, x_42);
lean_ctor_set(x_51, 4, x_43);
lean_ctor_set(x_51, 5, x_44);
lean_ctor_set(x_23, 0, x_51);
if (lean_is_scalar(x_9)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_9;
 lean_ctor_set_tag(x_52, 1);
}
lean_ctor_set(x_52, 0, x_26);
lean_ctor_set(x_52, 1, x_23);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_53 = lean_ctor_get(x_23, 1);
x_54 = lean_ctor_get(x_23, 2);
x_55 = lean_ctor_get(x_23, 3);
x_56 = lean_ctor_get(x_23, 4);
x_57 = lean_ctor_get(x_23, 5);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_23);
x_58 = lean_ctor_get(x_24, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_24, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_24, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_24, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_24, 5);
lean_inc(x_62);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 lean_ctor_release(x_24, 4);
 lean_ctor_release(x_24, 5);
 x_63 = x_24;
} else {
 lean_dec_ref(x_24);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_25, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_25, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_25, 3);
lean_inc(x_66);
x_67 = lean_ctor_get(x_25, 4);
lean_inc(x_67);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 lean_ctor_release(x_25, 4);
 x_68 = x_25;
} else {
 lean_dec_ref(x_25);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 5, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_65);
lean_ctor_set(x_69, 2, x_21);
lean_ctor_set(x_69, 3, x_66);
lean_ctor_set(x_69, 4, x_67);
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(0, 6, 0);
} else {
 x_70 = x_63;
}
lean_ctor_set(x_70, 0, x_58);
lean_ctor_set(x_70, 1, x_59);
lean_ctor_set(x_70, 2, x_69);
lean_ctor_set(x_70, 3, x_60);
lean_ctor_set(x_70, 4, x_61);
lean_ctor_set(x_70, 5, x_62);
x_71 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_53);
lean_ctor_set(x_71, 2, x_54);
lean_ctor_set(x_71, 3, x_55);
lean_ctor_set(x_71, 4, x_56);
lean_ctor_set(x_71, 5, x_57);
if (lean_is_scalar(x_9)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_9;
 lean_ctor_set_tag(x_72, 1);
}
lean_ctor_set(x_72, 0, x_26);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_23, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_22, 0);
lean_inc(x_75);
lean_dec(x_22);
x_76 = !lean_is_exclusive(x_23);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_23, 0);
lean_dec(x_77);
x_78 = !lean_is_exclusive(x_73);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_73, 2);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_74);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_74, 2);
lean_dec(x_81);
lean_ctor_set(x_74, 2, x_21);
if (lean_is_scalar(x_9)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_9;
}
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_23);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_74, 0);
x_84 = lean_ctor_get(x_74, 1);
x_85 = lean_ctor_get(x_74, 3);
x_86 = lean_ctor_get(x_74, 4);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_74);
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_84);
lean_ctor_set(x_87, 2, x_21);
lean_ctor_set(x_87, 3, x_85);
lean_ctor_set(x_87, 4, x_86);
lean_ctor_set(x_73, 2, x_87);
if (lean_is_scalar(x_9)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_9;
}
lean_ctor_set(x_88, 0, x_75);
lean_ctor_set(x_88, 1, x_23);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_89 = lean_ctor_get(x_73, 0);
x_90 = lean_ctor_get(x_73, 1);
x_91 = lean_ctor_get(x_73, 3);
x_92 = lean_ctor_get(x_73, 4);
x_93 = lean_ctor_get(x_73, 5);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_73);
x_94 = lean_ctor_get(x_74, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_74, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_74, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_74, 4);
lean_inc(x_97);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 lean_ctor_release(x_74, 4);
 x_98 = x_74;
} else {
 lean_dec_ref(x_74);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(0, 5, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_94);
lean_ctor_set(x_99, 1, x_95);
lean_ctor_set(x_99, 2, x_21);
lean_ctor_set(x_99, 3, x_96);
lean_ctor_set(x_99, 4, x_97);
x_100 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_100, 0, x_89);
lean_ctor_set(x_100, 1, x_90);
lean_ctor_set(x_100, 2, x_99);
lean_ctor_set(x_100, 3, x_91);
lean_ctor_set(x_100, 4, x_92);
lean_ctor_set(x_100, 5, x_93);
lean_ctor_set(x_23, 0, x_100);
if (lean_is_scalar(x_9)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_9;
}
lean_ctor_set(x_101, 0, x_75);
lean_ctor_set(x_101, 1, x_23);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_102 = lean_ctor_get(x_23, 1);
x_103 = lean_ctor_get(x_23, 2);
x_104 = lean_ctor_get(x_23, 3);
x_105 = lean_ctor_get(x_23, 4);
x_106 = lean_ctor_get(x_23, 5);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_23);
x_107 = lean_ctor_get(x_73, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_73, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_73, 3);
lean_inc(x_109);
x_110 = lean_ctor_get(x_73, 4);
lean_inc(x_110);
x_111 = lean_ctor_get(x_73, 5);
lean_inc(x_111);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 lean_ctor_release(x_73, 3);
 lean_ctor_release(x_73, 4);
 lean_ctor_release(x_73, 5);
 x_112 = x_73;
} else {
 lean_dec_ref(x_73);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_74, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_74, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_74, 3);
lean_inc(x_115);
x_116 = lean_ctor_get(x_74, 4);
lean_inc(x_116);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 lean_ctor_release(x_74, 4);
 x_117 = x_74;
} else {
 lean_dec_ref(x_74);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 5, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_113);
lean_ctor_set(x_118, 1, x_114);
lean_ctor_set(x_118, 2, x_21);
lean_ctor_set(x_118, 3, x_115);
lean_ctor_set(x_118, 4, x_116);
if (lean_is_scalar(x_112)) {
 x_119 = lean_alloc_ctor(0, 6, 0);
} else {
 x_119 = x_112;
}
lean_ctor_set(x_119, 0, x_107);
lean_ctor_set(x_119, 1, x_108);
lean_ctor_set(x_119, 2, x_118);
lean_ctor_set(x_119, 3, x_109);
lean_ctor_set(x_119, 4, x_110);
lean_ctor_set(x_119, 5, x_111);
x_120 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_102);
lean_ctor_set(x_120, 2, x_103);
lean_ctor_set(x_120, 3, x_104);
lean_ctor_set(x_120, 4, x_105);
lean_ctor_set(x_120, 5, x_106);
if (lean_is_scalar(x_9)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_9;
}
lean_ctor_set(x_121, 0, x_75);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_14, 0);
x_139 = lean_ctor_get(x_14, 3);
x_140 = lean_ctor_get(x_14, 4);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_14);
lean_inc(x_2);
x_141 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_1);
lean_ctor_set(x_141, 2, x_2);
lean_ctor_set(x_141, 3, x_139);
lean_ctor_set(x_141, 4, x_140);
lean_ctor_set(x_4, 0, x_141);
if (x_12 == 0)
{
lean_object* x_207; 
lean_dec(x_7);
lean_dec(x_2);
x_207 = lean_box(0);
x_142 = x_207;
goto block_206;
}
else
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_unsigned_to_nat(0u);
x_209 = l_Array_isEqvAux___main___at_Lean_Elab_Term_withLocalContext___spec__1(x_2, x_7, lean_box(0), x_2, x_7, x_208);
lean_dec(x_7);
lean_dec(x_2);
if (x_209 == 0)
{
lean_object* x_210; 
x_210 = lean_box(0);
x_142 = x_210;
goto block_206;
}
else
{
lean_object* x_211; 
lean_dec(x_9);
x_211 = lean_apply_2(x_3, x_4, x_8);
return x_211;
}
}
block_206:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_142);
x_143 = lean_ctor_get(x_8, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_143, 2);
lean_inc(x_144);
lean_dec(x_143);
x_145 = lean_ctor_get(x_144, 2);
lean_inc(x_145);
lean_dec(x_144);
x_197 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_8);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
x_199 = lean_apply_2(x_3, x_4, x_198);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_200);
x_146 = x_202;
x_147 = x_201;
goto block_196;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_199, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_199, 1);
lean_inc(x_204);
lean_dec(x_199);
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_203);
x_146 = x_205;
x_147 = x_204;
goto block_196;
}
block_196:
{
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_148, 2);
lean_inc(x_149);
x_150 = lean_ctor_get(x_146, 0);
lean_inc(x_150);
lean_dec(x_146);
x_151 = lean_ctor_get(x_147, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_147, 2);
lean_inc(x_152);
x_153 = lean_ctor_get(x_147, 3);
lean_inc(x_153);
x_154 = lean_ctor_get(x_147, 4);
lean_inc(x_154);
x_155 = lean_ctor_get(x_147, 5);
lean_inc(x_155);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 lean_ctor_release(x_147, 2);
 lean_ctor_release(x_147, 3);
 lean_ctor_release(x_147, 4);
 lean_ctor_release(x_147, 5);
 x_156 = x_147;
} else {
 lean_dec_ref(x_147);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_148, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_148, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_148, 3);
lean_inc(x_159);
x_160 = lean_ctor_get(x_148, 4);
lean_inc(x_160);
x_161 = lean_ctor_get(x_148, 5);
lean_inc(x_161);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 lean_ctor_release(x_148, 2);
 lean_ctor_release(x_148, 3);
 lean_ctor_release(x_148, 4);
 lean_ctor_release(x_148, 5);
 x_162 = x_148;
} else {
 lean_dec_ref(x_148);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_149, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_149, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_149, 3);
lean_inc(x_165);
x_166 = lean_ctor_get(x_149, 4);
lean_inc(x_166);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 lean_ctor_release(x_149, 2);
 lean_ctor_release(x_149, 3);
 lean_ctor_release(x_149, 4);
 x_167 = x_149;
} else {
 lean_dec_ref(x_149);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(0, 5, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_163);
lean_ctor_set(x_168, 1, x_164);
lean_ctor_set(x_168, 2, x_145);
lean_ctor_set(x_168, 3, x_165);
lean_ctor_set(x_168, 4, x_166);
if (lean_is_scalar(x_162)) {
 x_169 = lean_alloc_ctor(0, 6, 0);
} else {
 x_169 = x_162;
}
lean_ctor_set(x_169, 0, x_157);
lean_ctor_set(x_169, 1, x_158);
lean_ctor_set(x_169, 2, x_168);
lean_ctor_set(x_169, 3, x_159);
lean_ctor_set(x_169, 4, x_160);
lean_ctor_set(x_169, 5, x_161);
if (lean_is_scalar(x_156)) {
 x_170 = lean_alloc_ctor(0, 6, 0);
} else {
 x_170 = x_156;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_151);
lean_ctor_set(x_170, 2, x_152);
lean_ctor_set(x_170, 3, x_153);
lean_ctor_set(x_170, 4, x_154);
lean_ctor_set(x_170, 5, x_155);
if (lean_is_scalar(x_9)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_9;
 lean_ctor_set_tag(x_171, 1);
}
lean_ctor_set(x_171, 0, x_150);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_172 = lean_ctor_get(x_147, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_172, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_146, 0);
lean_inc(x_174);
lean_dec(x_146);
x_175 = lean_ctor_get(x_147, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_147, 2);
lean_inc(x_176);
x_177 = lean_ctor_get(x_147, 3);
lean_inc(x_177);
x_178 = lean_ctor_get(x_147, 4);
lean_inc(x_178);
x_179 = lean_ctor_get(x_147, 5);
lean_inc(x_179);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 lean_ctor_release(x_147, 2);
 lean_ctor_release(x_147, 3);
 lean_ctor_release(x_147, 4);
 lean_ctor_release(x_147, 5);
 x_180 = x_147;
} else {
 lean_dec_ref(x_147);
 x_180 = lean_box(0);
}
x_181 = lean_ctor_get(x_172, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_172, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_172, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_172, 4);
lean_inc(x_184);
x_185 = lean_ctor_get(x_172, 5);
lean_inc(x_185);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 lean_ctor_release(x_172, 2);
 lean_ctor_release(x_172, 3);
 lean_ctor_release(x_172, 4);
 lean_ctor_release(x_172, 5);
 x_186 = x_172;
} else {
 lean_dec_ref(x_172);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_173, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_173, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_173, 3);
lean_inc(x_189);
x_190 = lean_ctor_get(x_173, 4);
lean_inc(x_190);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 lean_ctor_release(x_173, 2);
 lean_ctor_release(x_173, 3);
 lean_ctor_release(x_173, 4);
 x_191 = x_173;
} else {
 lean_dec_ref(x_173);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(0, 5, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_187);
lean_ctor_set(x_192, 1, x_188);
lean_ctor_set(x_192, 2, x_145);
lean_ctor_set(x_192, 3, x_189);
lean_ctor_set(x_192, 4, x_190);
if (lean_is_scalar(x_186)) {
 x_193 = lean_alloc_ctor(0, 6, 0);
} else {
 x_193 = x_186;
}
lean_ctor_set(x_193, 0, x_181);
lean_ctor_set(x_193, 1, x_182);
lean_ctor_set(x_193, 2, x_192);
lean_ctor_set(x_193, 3, x_183);
lean_ctor_set(x_193, 4, x_184);
lean_ctor_set(x_193, 5, x_185);
if (lean_is_scalar(x_180)) {
 x_194 = lean_alloc_ctor(0, 6, 0);
} else {
 x_194 = x_180;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_175);
lean_ctor_set(x_194, 2, x_176);
lean_ctor_set(x_194, 3, x_177);
lean_ctor_set(x_194, 4, x_178);
lean_ctor_set(x_194, 5, x_179);
if (lean_is_scalar(x_9)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_9;
}
lean_ctor_set(x_195, 0, x_174);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; uint8_t x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_212 = lean_ctor_get(x_4, 0);
x_213 = lean_ctor_get(x_4, 1);
x_214 = lean_ctor_get(x_4, 2);
x_215 = lean_ctor_get(x_4, 3);
x_216 = lean_ctor_get(x_4, 4);
x_217 = lean_ctor_get(x_4, 5);
x_218 = lean_ctor_get(x_4, 6);
x_219 = lean_ctor_get(x_4, 7);
x_220 = lean_ctor_get(x_4, 8);
x_221 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_222 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_223 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_224 = lean_ctor_get(x_4, 9);
lean_inc(x_224);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_4);
x_225 = lean_ctor_get(x_212, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_212, 3);
lean_inc(x_226);
x_227 = lean_ctor_get(x_212, 4);
lean_inc(x_227);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 lean_ctor_release(x_212, 2);
 lean_ctor_release(x_212, 3);
 lean_ctor_release(x_212, 4);
 x_228 = x_212;
} else {
 lean_dec_ref(x_212);
 x_228 = lean_box(0);
}
lean_inc(x_2);
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(0, 5, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_225);
lean_ctor_set(x_229, 1, x_1);
lean_ctor_set(x_229, 2, x_2);
lean_ctor_set(x_229, 3, x_226);
lean_ctor_set(x_229, 4, x_227);
x_230 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_213);
lean_ctor_set(x_230, 2, x_214);
lean_ctor_set(x_230, 3, x_215);
lean_ctor_set(x_230, 4, x_216);
lean_ctor_set(x_230, 5, x_217);
lean_ctor_set(x_230, 6, x_218);
lean_ctor_set(x_230, 7, x_219);
lean_ctor_set(x_230, 8, x_220);
lean_ctor_set(x_230, 9, x_224);
lean_ctor_set_uint8(x_230, sizeof(void*)*10, x_221);
lean_ctor_set_uint8(x_230, sizeof(void*)*10 + 1, x_222);
lean_ctor_set_uint8(x_230, sizeof(void*)*10 + 2, x_223);
if (x_12 == 0)
{
lean_object* x_296; 
lean_dec(x_7);
lean_dec(x_2);
x_296 = lean_box(0);
x_231 = x_296;
goto block_295;
}
else
{
lean_object* x_297; uint8_t x_298; 
x_297 = lean_unsigned_to_nat(0u);
x_298 = l_Array_isEqvAux___main___at_Lean_Elab_Term_withLocalContext___spec__1(x_2, x_7, lean_box(0), x_2, x_7, x_297);
lean_dec(x_7);
lean_dec(x_2);
if (x_298 == 0)
{
lean_object* x_299; 
x_299 = lean_box(0);
x_231 = x_299;
goto block_295;
}
else
{
lean_object* x_300; 
lean_dec(x_9);
x_300 = lean_apply_2(x_3, x_230, x_8);
return x_300;
}
}
block_295:
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_231);
x_232 = lean_ctor_get(x_8, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_232, 2);
lean_inc(x_233);
lean_dec(x_232);
x_234 = lean_ctor_get(x_233, 2);
lean_inc(x_234);
lean_dec(x_233);
x_286 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_8);
x_287 = lean_ctor_get(x_286, 1);
lean_inc(x_287);
lean_dec(x_286);
x_288 = lean_apply_2(x_3, x_230, x_287);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_289);
x_235 = x_291;
x_236 = x_290;
goto block_285;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_288, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_288, 1);
lean_inc(x_293);
lean_dec(x_288);
x_294 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_294, 0, x_292);
x_235 = x_294;
x_236 = x_293;
goto block_285;
}
block_285:
{
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_237, 2);
lean_inc(x_238);
x_239 = lean_ctor_get(x_235, 0);
lean_inc(x_239);
lean_dec(x_235);
x_240 = lean_ctor_get(x_236, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_236, 2);
lean_inc(x_241);
x_242 = lean_ctor_get(x_236, 3);
lean_inc(x_242);
x_243 = lean_ctor_get(x_236, 4);
lean_inc(x_243);
x_244 = lean_ctor_get(x_236, 5);
lean_inc(x_244);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 lean_ctor_release(x_236, 2);
 lean_ctor_release(x_236, 3);
 lean_ctor_release(x_236, 4);
 lean_ctor_release(x_236, 5);
 x_245 = x_236;
} else {
 lean_dec_ref(x_236);
 x_245 = lean_box(0);
}
x_246 = lean_ctor_get(x_237, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_237, 1);
lean_inc(x_247);
x_248 = lean_ctor_get(x_237, 3);
lean_inc(x_248);
x_249 = lean_ctor_get(x_237, 4);
lean_inc(x_249);
x_250 = lean_ctor_get(x_237, 5);
lean_inc(x_250);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 lean_ctor_release(x_237, 2);
 lean_ctor_release(x_237, 3);
 lean_ctor_release(x_237, 4);
 lean_ctor_release(x_237, 5);
 x_251 = x_237;
} else {
 lean_dec_ref(x_237);
 x_251 = lean_box(0);
}
x_252 = lean_ctor_get(x_238, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_238, 1);
lean_inc(x_253);
x_254 = lean_ctor_get(x_238, 3);
lean_inc(x_254);
x_255 = lean_ctor_get(x_238, 4);
lean_inc(x_255);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 lean_ctor_release(x_238, 2);
 lean_ctor_release(x_238, 3);
 lean_ctor_release(x_238, 4);
 x_256 = x_238;
} else {
 lean_dec_ref(x_238);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(0, 5, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_252);
lean_ctor_set(x_257, 1, x_253);
lean_ctor_set(x_257, 2, x_234);
lean_ctor_set(x_257, 3, x_254);
lean_ctor_set(x_257, 4, x_255);
if (lean_is_scalar(x_251)) {
 x_258 = lean_alloc_ctor(0, 6, 0);
} else {
 x_258 = x_251;
}
lean_ctor_set(x_258, 0, x_246);
lean_ctor_set(x_258, 1, x_247);
lean_ctor_set(x_258, 2, x_257);
lean_ctor_set(x_258, 3, x_248);
lean_ctor_set(x_258, 4, x_249);
lean_ctor_set(x_258, 5, x_250);
if (lean_is_scalar(x_245)) {
 x_259 = lean_alloc_ctor(0, 6, 0);
} else {
 x_259 = x_245;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_240);
lean_ctor_set(x_259, 2, x_241);
lean_ctor_set(x_259, 3, x_242);
lean_ctor_set(x_259, 4, x_243);
lean_ctor_set(x_259, 5, x_244);
if (lean_is_scalar(x_9)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_9;
 lean_ctor_set_tag(x_260, 1);
}
lean_ctor_set(x_260, 0, x_239);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_261 = lean_ctor_get(x_236, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_261, 2);
lean_inc(x_262);
x_263 = lean_ctor_get(x_235, 0);
lean_inc(x_263);
lean_dec(x_235);
x_264 = lean_ctor_get(x_236, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_236, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_236, 3);
lean_inc(x_266);
x_267 = lean_ctor_get(x_236, 4);
lean_inc(x_267);
x_268 = lean_ctor_get(x_236, 5);
lean_inc(x_268);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 lean_ctor_release(x_236, 2);
 lean_ctor_release(x_236, 3);
 lean_ctor_release(x_236, 4);
 lean_ctor_release(x_236, 5);
 x_269 = x_236;
} else {
 lean_dec_ref(x_236);
 x_269 = lean_box(0);
}
x_270 = lean_ctor_get(x_261, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_261, 1);
lean_inc(x_271);
x_272 = lean_ctor_get(x_261, 3);
lean_inc(x_272);
x_273 = lean_ctor_get(x_261, 4);
lean_inc(x_273);
x_274 = lean_ctor_get(x_261, 5);
lean_inc(x_274);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 lean_ctor_release(x_261, 3);
 lean_ctor_release(x_261, 4);
 lean_ctor_release(x_261, 5);
 x_275 = x_261;
} else {
 lean_dec_ref(x_261);
 x_275 = lean_box(0);
}
x_276 = lean_ctor_get(x_262, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_262, 1);
lean_inc(x_277);
x_278 = lean_ctor_get(x_262, 3);
lean_inc(x_278);
x_279 = lean_ctor_get(x_262, 4);
lean_inc(x_279);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 lean_ctor_release(x_262, 2);
 lean_ctor_release(x_262, 3);
 lean_ctor_release(x_262, 4);
 x_280 = x_262;
} else {
 lean_dec_ref(x_262);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(0, 5, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_276);
lean_ctor_set(x_281, 1, x_277);
lean_ctor_set(x_281, 2, x_234);
lean_ctor_set(x_281, 3, x_278);
lean_ctor_set(x_281, 4, x_279);
if (lean_is_scalar(x_275)) {
 x_282 = lean_alloc_ctor(0, 6, 0);
} else {
 x_282 = x_275;
}
lean_ctor_set(x_282, 0, x_270);
lean_ctor_set(x_282, 1, x_271);
lean_ctor_set(x_282, 2, x_281);
lean_ctor_set(x_282, 3, x_272);
lean_ctor_set(x_282, 4, x_273);
lean_ctor_set(x_282, 5, x_274);
if (lean_is_scalar(x_269)) {
 x_283 = lean_alloc_ctor(0, 6, 0);
} else {
 x_283 = x_269;
}
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_264);
lean_ctor_set(x_283, 2, x_265);
lean_ctor_set(x_283, 3, x_266);
lean_ctor_set(x_283, 4, x_267);
lean_ctor_set(x_283, 5, x_268);
if (lean_is_scalar(x_9)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_9;
}
lean_ctor_set(x_284, 0, x_263);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_withLocalContext(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withLocalContext___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_Elab_Term_withLocalContext___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at_Lean_Elab_Term_withLocalContext___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_Elab_Term_withMVarContext___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_LocalInstance_beq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Term_withMVarContext___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
x_5 = l_Lean_Elab_Term_getMVarDecl(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_9 = x_5;
} else {
 lean_dec_ref(x_5);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 7);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 8);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_21 = lean_ctor_get(x_3, 9);
lean_inc(x_21);
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_6, 2);
x_24 = lean_ctor_get(x_6, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_7, 4);
lean_inc(x_26);
x_27 = lean_array_get_size(x_23);
x_28 = lean_array_get_size(x_26);
x_29 = lean_nat_dec_eq(x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
lean_inc(x_26);
lean_ctor_set(x_6, 2, x_26);
lean_ctor_set(x_6, 1, x_25);
x_30 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_30, 0, x_6);
lean_ctor_set(x_30, 1, x_10);
lean_ctor_set(x_30, 2, x_11);
lean_ctor_set(x_30, 3, x_12);
lean_ctor_set(x_30, 4, x_13);
lean_ctor_set(x_30, 5, x_14);
lean_ctor_set(x_30, 6, x_15);
lean_ctor_set(x_30, 7, x_16);
lean_ctor_set(x_30, 8, x_17);
lean_ctor_set(x_30, 9, x_21);
lean_ctor_set_uint8(x_30, sizeof(void*)*10, x_18);
lean_ctor_set_uint8(x_30, sizeof(void*)*10 + 1, x_19);
lean_ctor_set_uint8(x_30, sizeof(void*)*10 + 2, x_20);
if (x_29 == 0)
{
lean_object* x_31; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
x_31 = lean_apply_2(x_2, x_30, x_8);
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Array_isEqvAux___main___at_Lean_Elab_Term_withMVarContext___spec__1(x_3, x_7, lean_box(0), x_23, x_26, x_32);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_7);
lean_dec(x_3);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_9);
x_34 = lean_apply_2(x_2, x_30, x_8);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_35 = lean_ctor_get(x_8, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 2);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_36, 2);
lean_inc(x_37);
lean_dec(x_36);
x_139 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_8);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_apply_2(x_2, x_30, x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_142);
x_38 = x_144;
x_39 = x_143;
goto block_138;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_141, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
lean_dec(x_141);
x_147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_147, 0, x_145);
x_38 = x_147;
x_39 = x_146;
goto block_138;
}
block_138:
{
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_39, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_40, 2);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_41);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_41, 2);
lean_dec(x_48);
lean_ctor_set(x_41, 2, x_37);
if (lean_is_scalar(x_9)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_9;
 lean_ctor_set_tag(x_49, 1);
}
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_39);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_41, 0);
x_51 = lean_ctor_get(x_41, 1);
x_52 = lean_ctor_get(x_41, 3);
x_53 = lean_ctor_get(x_41, 4);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_41);
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set(x_54, 2, x_37);
lean_ctor_set(x_54, 3, x_52);
lean_ctor_set(x_54, 4, x_53);
lean_ctor_set(x_40, 2, x_54);
if (lean_is_scalar(x_9)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_9;
 lean_ctor_set_tag(x_55, 1);
}
lean_ctor_set(x_55, 0, x_42);
lean_ctor_set(x_55, 1, x_39);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_56 = lean_ctor_get(x_40, 0);
x_57 = lean_ctor_get(x_40, 1);
x_58 = lean_ctor_get(x_40, 3);
x_59 = lean_ctor_get(x_40, 4);
x_60 = lean_ctor_get(x_40, 5);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_40);
x_61 = lean_ctor_get(x_41, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_41, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_41, 3);
lean_inc(x_63);
x_64 = lean_ctor_get(x_41, 4);
lean_inc(x_64);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 x_65 = x_41;
} else {
 lean_dec_ref(x_41);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 5, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_62);
lean_ctor_set(x_66, 2, x_37);
lean_ctor_set(x_66, 3, x_63);
lean_ctor_set(x_66, 4, x_64);
x_67 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_67, 0, x_56);
lean_ctor_set(x_67, 1, x_57);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set(x_67, 3, x_58);
lean_ctor_set(x_67, 4, x_59);
lean_ctor_set(x_67, 5, x_60);
lean_ctor_set(x_39, 0, x_67);
if (lean_is_scalar(x_9)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_9;
 lean_ctor_set_tag(x_68, 1);
}
lean_ctor_set(x_68, 0, x_42);
lean_ctor_set(x_68, 1, x_39);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_69 = lean_ctor_get(x_39, 1);
x_70 = lean_ctor_get(x_39, 2);
x_71 = lean_ctor_get(x_39, 3);
x_72 = lean_ctor_get(x_39, 4);
x_73 = lean_ctor_get(x_39, 5);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_39);
x_74 = lean_ctor_get(x_40, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_40, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_40, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_40, 4);
lean_inc(x_77);
x_78 = lean_ctor_get(x_40, 5);
lean_inc(x_78);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 x_79 = x_40;
} else {
 lean_dec_ref(x_40);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_41, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_41, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_41, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_41, 4);
lean_inc(x_83);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 x_84 = x_41;
} else {
 lean_dec_ref(x_41);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 5, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_80);
lean_ctor_set(x_85, 1, x_81);
lean_ctor_set(x_85, 2, x_37);
lean_ctor_set(x_85, 3, x_82);
lean_ctor_set(x_85, 4, x_83);
if (lean_is_scalar(x_79)) {
 x_86 = lean_alloc_ctor(0, 6, 0);
} else {
 x_86 = x_79;
}
lean_ctor_set(x_86, 0, x_74);
lean_ctor_set(x_86, 1, x_75);
lean_ctor_set(x_86, 2, x_85);
lean_ctor_set(x_86, 3, x_76);
lean_ctor_set(x_86, 4, x_77);
lean_ctor_set(x_86, 5, x_78);
x_87 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_69);
lean_ctor_set(x_87, 2, x_70);
lean_ctor_set(x_87, 3, x_71);
lean_ctor_set(x_87, 4, x_72);
lean_ctor_set(x_87, 5, x_73);
if (lean_is_scalar(x_9)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_9;
 lean_ctor_set_tag(x_88, 1);
}
lean_ctor_set(x_88, 0, x_42);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_39, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_38, 0);
lean_inc(x_91);
lean_dec(x_38);
x_92 = !lean_is_exclusive(x_39);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_39, 0);
lean_dec(x_93);
x_94 = !lean_is_exclusive(x_89);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_89, 2);
lean_dec(x_95);
x_96 = !lean_is_exclusive(x_90);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_90, 2);
lean_dec(x_97);
lean_ctor_set(x_90, 2, x_37);
if (lean_is_scalar(x_9)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_9;
}
lean_ctor_set(x_98, 0, x_91);
lean_ctor_set(x_98, 1, x_39);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_90, 0);
x_100 = lean_ctor_get(x_90, 1);
x_101 = lean_ctor_get(x_90, 3);
x_102 = lean_ctor_get(x_90, 4);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_90);
x_103 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_100);
lean_ctor_set(x_103, 2, x_37);
lean_ctor_set(x_103, 3, x_101);
lean_ctor_set(x_103, 4, x_102);
lean_ctor_set(x_89, 2, x_103);
if (lean_is_scalar(x_9)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_9;
}
lean_ctor_set(x_104, 0, x_91);
lean_ctor_set(x_104, 1, x_39);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_105 = lean_ctor_get(x_89, 0);
x_106 = lean_ctor_get(x_89, 1);
x_107 = lean_ctor_get(x_89, 3);
x_108 = lean_ctor_get(x_89, 4);
x_109 = lean_ctor_get(x_89, 5);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_89);
x_110 = lean_ctor_get(x_90, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_90, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_90, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_90, 4);
lean_inc(x_113);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 lean_ctor_release(x_90, 2);
 lean_ctor_release(x_90, 3);
 lean_ctor_release(x_90, 4);
 x_114 = x_90;
} else {
 lean_dec_ref(x_90);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 5, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_111);
lean_ctor_set(x_115, 2, x_37);
lean_ctor_set(x_115, 3, x_112);
lean_ctor_set(x_115, 4, x_113);
x_116 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_116, 0, x_105);
lean_ctor_set(x_116, 1, x_106);
lean_ctor_set(x_116, 2, x_115);
lean_ctor_set(x_116, 3, x_107);
lean_ctor_set(x_116, 4, x_108);
lean_ctor_set(x_116, 5, x_109);
lean_ctor_set(x_39, 0, x_116);
if (lean_is_scalar(x_9)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_9;
}
lean_ctor_set(x_117, 0, x_91);
lean_ctor_set(x_117, 1, x_39);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_118 = lean_ctor_get(x_39, 1);
x_119 = lean_ctor_get(x_39, 2);
x_120 = lean_ctor_get(x_39, 3);
x_121 = lean_ctor_get(x_39, 4);
x_122 = lean_ctor_get(x_39, 5);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_39);
x_123 = lean_ctor_get(x_89, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_89, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_89, 3);
lean_inc(x_125);
x_126 = lean_ctor_get(x_89, 4);
lean_inc(x_126);
x_127 = lean_ctor_get(x_89, 5);
lean_inc(x_127);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 lean_ctor_release(x_89, 4);
 lean_ctor_release(x_89, 5);
 x_128 = x_89;
} else {
 lean_dec_ref(x_89);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_90, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_90, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_90, 3);
lean_inc(x_131);
x_132 = lean_ctor_get(x_90, 4);
lean_inc(x_132);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 lean_ctor_release(x_90, 2);
 lean_ctor_release(x_90, 3);
 lean_ctor_release(x_90, 4);
 x_133 = x_90;
} else {
 lean_dec_ref(x_90);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 5, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set(x_134, 1, x_130);
lean_ctor_set(x_134, 2, x_37);
lean_ctor_set(x_134, 3, x_131);
lean_ctor_set(x_134, 4, x_132);
if (lean_is_scalar(x_128)) {
 x_135 = lean_alloc_ctor(0, 6, 0);
} else {
 x_135 = x_128;
}
lean_ctor_set(x_135, 0, x_123);
lean_ctor_set(x_135, 1, x_124);
lean_ctor_set(x_135, 2, x_134);
lean_ctor_set(x_135, 3, x_125);
lean_ctor_set(x_135, 4, x_126);
lean_ctor_set(x_135, 5, x_127);
x_136 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_118);
lean_ctor_set(x_136, 2, x_119);
lean_ctor_set(x_136, 3, x_120);
lean_ctor_set(x_136, 4, x_121);
lean_ctor_set(x_136, 5, x_122);
if (lean_is_scalar(x_9)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_9;
}
lean_ctor_set(x_137, 0, x_91);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; 
x_148 = lean_ctor_get(x_6, 0);
x_149 = lean_ctor_get(x_6, 2);
x_150 = lean_ctor_get(x_6, 3);
x_151 = lean_ctor_get(x_6, 4);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_6);
x_152 = lean_ctor_get(x_7, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_7, 4);
lean_inc(x_153);
x_154 = lean_array_get_size(x_149);
x_155 = lean_array_get_size(x_153);
x_156 = lean_nat_dec_eq(x_154, x_155);
lean_dec(x_155);
lean_dec(x_154);
lean_inc(x_153);
x_157 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_157, 0, x_148);
lean_ctor_set(x_157, 1, x_152);
lean_ctor_set(x_157, 2, x_153);
lean_ctor_set(x_157, 3, x_150);
lean_ctor_set(x_157, 4, x_151);
x_158 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_10);
lean_ctor_set(x_158, 2, x_11);
lean_ctor_set(x_158, 3, x_12);
lean_ctor_set(x_158, 4, x_13);
lean_ctor_set(x_158, 5, x_14);
lean_ctor_set(x_158, 6, x_15);
lean_ctor_set(x_158, 7, x_16);
lean_ctor_set(x_158, 8, x_17);
lean_ctor_set(x_158, 9, x_21);
lean_ctor_set_uint8(x_158, sizeof(void*)*10, x_18);
lean_ctor_set_uint8(x_158, sizeof(void*)*10 + 1, x_19);
lean_ctor_set_uint8(x_158, sizeof(void*)*10 + 2, x_20);
if (x_156 == 0)
{
lean_object* x_159; 
lean_dec(x_153);
lean_dec(x_149);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
x_159 = lean_apply_2(x_2, x_158, x_8);
return x_159;
}
else
{
lean_object* x_160; uint8_t x_161; 
x_160 = lean_unsigned_to_nat(0u);
x_161 = l_Array_isEqvAux___main___at_Lean_Elab_Term_withMVarContext___spec__1(x_3, x_7, lean_box(0), x_149, x_153, x_160);
lean_dec(x_153);
lean_dec(x_149);
lean_dec(x_7);
lean_dec(x_3);
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_9);
x_162 = lean_apply_2(x_2, x_158, x_8);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_163 = lean_ctor_get(x_8, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_163, 2);
lean_inc(x_164);
lean_dec(x_163);
x_165 = lean_ctor_get(x_164, 2);
lean_inc(x_165);
lean_dec(x_164);
x_217 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_8);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
x_219 = lean_apply_2(x_2, x_158, x_218);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_220);
x_166 = x_222;
x_167 = x_221;
goto block_216;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_219, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_219, 1);
lean_inc(x_224);
lean_dec(x_219);
x_225 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_225, 0, x_223);
x_166 = x_225;
x_167 = x_224;
goto block_216;
}
block_216:
{
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_168, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_166, 0);
lean_inc(x_170);
lean_dec(x_166);
x_171 = lean_ctor_get(x_167, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_167, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_167, 3);
lean_inc(x_173);
x_174 = lean_ctor_get(x_167, 4);
lean_inc(x_174);
x_175 = lean_ctor_get(x_167, 5);
lean_inc(x_175);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 lean_ctor_release(x_167, 2);
 lean_ctor_release(x_167, 3);
 lean_ctor_release(x_167, 4);
 lean_ctor_release(x_167, 5);
 x_176 = x_167;
} else {
 lean_dec_ref(x_167);
 x_176 = lean_box(0);
}
x_177 = lean_ctor_get(x_168, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_168, 1);
lean_inc(x_178);
x_179 = lean_ctor_get(x_168, 3);
lean_inc(x_179);
x_180 = lean_ctor_get(x_168, 4);
lean_inc(x_180);
x_181 = lean_ctor_get(x_168, 5);
lean_inc(x_181);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 lean_ctor_release(x_168, 3);
 lean_ctor_release(x_168, 4);
 lean_ctor_release(x_168, 5);
 x_182 = x_168;
} else {
 lean_dec_ref(x_168);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_169, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_169, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_169, 3);
lean_inc(x_185);
x_186 = lean_ctor_get(x_169, 4);
lean_inc(x_186);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 lean_ctor_release(x_169, 2);
 lean_ctor_release(x_169, 3);
 lean_ctor_release(x_169, 4);
 x_187 = x_169;
} else {
 lean_dec_ref(x_169);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(0, 5, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_188, 2, x_165);
lean_ctor_set(x_188, 3, x_185);
lean_ctor_set(x_188, 4, x_186);
if (lean_is_scalar(x_182)) {
 x_189 = lean_alloc_ctor(0, 6, 0);
} else {
 x_189 = x_182;
}
lean_ctor_set(x_189, 0, x_177);
lean_ctor_set(x_189, 1, x_178);
lean_ctor_set(x_189, 2, x_188);
lean_ctor_set(x_189, 3, x_179);
lean_ctor_set(x_189, 4, x_180);
lean_ctor_set(x_189, 5, x_181);
if (lean_is_scalar(x_176)) {
 x_190 = lean_alloc_ctor(0, 6, 0);
} else {
 x_190 = x_176;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_171);
lean_ctor_set(x_190, 2, x_172);
lean_ctor_set(x_190, 3, x_173);
lean_ctor_set(x_190, 4, x_174);
lean_ctor_set(x_190, 5, x_175);
if (lean_is_scalar(x_9)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_9;
 lean_ctor_set_tag(x_191, 1);
}
lean_ctor_set(x_191, 0, x_170);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_192 = lean_ctor_get(x_167, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_192, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_166, 0);
lean_inc(x_194);
lean_dec(x_166);
x_195 = lean_ctor_get(x_167, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_167, 2);
lean_inc(x_196);
x_197 = lean_ctor_get(x_167, 3);
lean_inc(x_197);
x_198 = lean_ctor_get(x_167, 4);
lean_inc(x_198);
x_199 = lean_ctor_get(x_167, 5);
lean_inc(x_199);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 lean_ctor_release(x_167, 2);
 lean_ctor_release(x_167, 3);
 lean_ctor_release(x_167, 4);
 lean_ctor_release(x_167, 5);
 x_200 = x_167;
} else {
 lean_dec_ref(x_167);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get(x_192, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_192, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_192, 3);
lean_inc(x_203);
x_204 = lean_ctor_get(x_192, 4);
lean_inc(x_204);
x_205 = lean_ctor_get(x_192, 5);
lean_inc(x_205);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 lean_ctor_release(x_192, 2);
 lean_ctor_release(x_192, 3);
 lean_ctor_release(x_192, 4);
 lean_ctor_release(x_192, 5);
 x_206 = x_192;
} else {
 lean_dec_ref(x_192);
 x_206 = lean_box(0);
}
x_207 = lean_ctor_get(x_193, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_193, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_193, 3);
lean_inc(x_209);
x_210 = lean_ctor_get(x_193, 4);
lean_inc(x_210);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 lean_ctor_release(x_193, 4);
 x_211 = x_193;
} else {
 lean_dec_ref(x_193);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(0, 5, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_207);
lean_ctor_set(x_212, 1, x_208);
lean_ctor_set(x_212, 2, x_165);
lean_ctor_set(x_212, 3, x_209);
lean_ctor_set(x_212, 4, x_210);
if (lean_is_scalar(x_206)) {
 x_213 = lean_alloc_ctor(0, 6, 0);
} else {
 x_213 = x_206;
}
lean_ctor_set(x_213, 0, x_201);
lean_ctor_set(x_213, 1, x_202);
lean_ctor_set(x_213, 2, x_212);
lean_ctor_set(x_213, 3, x_203);
lean_ctor_set(x_213, 4, x_204);
lean_ctor_set(x_213, 5, x_205);
if (lean_is_scalar(x_200)) {
 x_214 = lean_alloc_ctor(0, 6, 0);
} else {
 x_214 = x_200;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_195);
lean_ctor_set(x_214, 2, x_196);
lean_ctor_set(x_214, 3, x_197);
lean_ctor_set(x_214, 4, x_198);
lean_ctor_set(x_214, 5, x_199);
if (lean_is_scalar(x_9)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_9;
}
lean_ctor_set(x_215, 0, x_194);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_withMVarContext(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withMVarContext___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_Elab_Term_withMVarContext___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at_Lean_Elab_Term_withMVarContext___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_withMVarContext___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_withMVarContext___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_mkInstMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = 1;
x_6 = lean_box(0);
lean_inc(x_2);
x_7 = l_Lean_Elab_Term_mkFreshExprMVar(x_4, x_5, x_6, x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Expr_mvarId_x21(x_8);
lean_inc(x_2);
lean_inc(x_10);
x_11 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_10, x_2, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_box(0);
x_16 = l_Lean_Elab_Term_registerSyntheticMVar(x_10, x_15, x_2, x_14);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_8);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_11, 0);
lean_dec(x_22);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* _init_l___private_Lean_Elab_Term_15__tryCoeSort___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CoeSort");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Term_15__tryCoeSort___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Term_15__tryCoeSort___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Term_15__tryCoeSort___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toStr___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Term_15__tryCoeSort___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Term_15__tryCoeSort___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Term_15__tryCoeSort___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Term_15__tryCoeSort___closed__4;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Term_15__tryCoeSort___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coeSort");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Term_15__tryCoeSort___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Term_15__tryCoeSort___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Term_15__tryCoeSort(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = 0;
x_6 = lean_box(0);
lean_inc(x_3);
x_7 = l_Lean_Elab_Term_mkFreshTypeMVar(x_5, x_6, x_3, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_Elab_Term_getLevel(x_1, x_3, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_3);
lean_inc(x_8);
x_13 = l_Lean_Elab_Term_getLevel(x_8, x_3, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Lean_Elab_Term_15__tryCoeSort___closed__2;
lean_inc(x_18);
x_20 = l_Lean_mkConst(x_19, x_18);
x_21 = l_Lean_mkAppStx___closed__9;
lean_inc(x_1);
x_22 = lean_array_push(x_21, x_1);
lean_inc(x_8);
x_23 = lean_array_push(x_22, x_8);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_23, x_23, x_24, x_20);
lean_dec(x_23);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = 1;
lean_inc(x_3);
x_28 = l_Lean_Elab_Term_mkFreshExprMVar(x_26, x_27, x_6, x_3, x_15);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Expr_mvarId_x21(x_29);
x_45 = lean_ctor_get(x_3, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_3, 4);
lean_inc(x_49);
x_50 = lean_ctor_get(x_3, 5);
lean_inc(x_50);
x_51 = lean_ctor_get(x_3, 6);
lean_inc(x_51);
x_52 = lean_ctor_get(x_3, 7);
lean_inc(x_52);
x_53 = lean_ctor_get(x_3, 8);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_55 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_56 = lean_ctor_get(x_3, 9);
lean_inc(x_56);
x_57 = 0;
x_58 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_58, 0, x_45);
lean_ctor_set(x_58, 1, x_46);
lean_ctor_set(x_58, 2, x_47);
lean_ctor_set(x_58, 3, x_48);
lean_ctor_set(x_58, 4, x_49);
lean_ctor_set(x_58, 5, x_50);
lean_ctor_set(x_58, 6, x_51);
lean_ctor_set(x_58, 7, x_52);
lean_ctor_set(x_58, 8, x_53);
lean_ctor_set(x_58, 9, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*10, x_54);
lean_ctor_set_uint8(x_58, sizeof(void*)*10 + 1, x_55);
lean_ctor_set_uint8(x_58, sizeof(void*)*10 + 2, x_57);
lean_inc(x_58);
x_59 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_31, x_58, x_30);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_29);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = l___private_Lean_Elab_Term_15__tryCoeSort___closed__4;
x_64 = l_Lean_Elab_Term_throwError___rarg(x_63, x_58, x_62);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_32 = x_65;
x_33 = x_66;
goto block_44;
}
else
{
uint8_t x_67; 
lean_dec(x_58);
lean_dec(x_3);
x_67 = !lean_is_exclusive(x_59);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_68 = lean_ctor_get(x_59, 0);
lean_dec(x_68);
x_69 = l___private_Lean_Elab_Term_15__tryCoeSort___closed__7;
x_70 = l_Lean_mkConst(x_69, x_18);
x_71 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_72 = lean_array_push(x_71, x_1);
x_73 = lean_array_push(x_72, x_8);
x_74 = lean_array_push(x_73, x_2);
x_75 = lean_array_push(x_74, x_29);
x_76 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_75, x_75, x_24, x_70);
lean_dec(x_75);
lean_ctor_set(x_59, 0, x_76);
return x_59;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_59, 1);
lean_inc(x_77);
lean_dec(x_59);
x_78 = l___private_Lean_Elab_Term_15__tryCoeSort___closed__7;
x_79 = l_Lean_mkConst(x_78, x_18);
x_80 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_81 = lean_array_push(x_80, x_1);
x_82 = lean_array_push(x_81, x_8);
x_83 = lean_array_push(x_82, x_2);
x_84 = lean_array_push(x_83, x_29);
x_85 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_84, x_84, x_24, x_79);
lean_dec(x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_77);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_58);
lean_dec(x_29);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_87 = lean_ctor_get(x_59, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_59, 1);
lean_inc(x_88);
lean_dec(x_59);
x_32 = x_87;
x_33 = x_88;
goto block_44;
}
block_44:
{
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 4);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l___private_Lean_Elab_Term_15__tryCoeSort___closed__5;
x_38 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Lean_Elab_Term_throwError___rarg(x_38, x_3, x_33);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = l___private_Lean_Elab_Term_15__tryCoeSort___closed__4;
x_41 = l_Lean_Elab_Term_throwError___rarg(x_40, x_3, x_33);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = l___private_Lean_Elab_Term_15__tryCoeSort___closed__4;
x_43 = l_Lean_Elab_Term_throwError___rarg(x_42, x_3, x_33);
return x_43;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_13);
if (x_89 == 0)
{
return x_13;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_13, 0);
x_91 = lean_ctor_get(x_13, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_13);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_10);
if (x_93 == 0)
{
return x_10;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_10, 0);
x_95 = lean_ctor_get(x_10, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_10);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
lean_object* l_Lean_Elab_Term_ensureType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Elab_Term_isType(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_Elab_Term_inferType(x_1, x_2, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_2);
x_11 = l_Lean_Elab_Term_mkFreshLevelMVar(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_mkSort(x_12);
lean_inc(x_2);
lean_inc(x_9);
x_15 = l_Lean_Elab_Term_isDefEq(x_9, x_14, x_2, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l___private_Lean_Elab_Term_15__tryCoeSort(x_9, x_1, x_2, x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_15, 0);
lean_dec(x_21);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_8);
if (x_28 == 0)
{
return x_8;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_8, 0);
x_30 = lean_ctor_get(x_8, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_8);
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
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_4);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_4, 0);
lean_dec(x_33);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_dec(x_4);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l_Lean_Elab_Term_elabType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Term_mkFreshLevelMVar(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_mkSort(x_5);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = 1;
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_Elab_Term_elabTerm(x_1, x_8, x_9, x_2, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 9);
x_15 = l_Lean_Elab_replaceRef(x_1, x_14);
lean_dec(x_14);
lean_dec(x_1);
lean_ctor_set(x_2, 9, x_15);
x_16 = l_Lean_Elab_Term_ensureType(x_11, x_2, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_2, 3);
x_21 = lean_ctor_get(x_2, 4);
x_22 = lean_ctor_get(x_2, 5);
x_23 = lean_ctor_get(x_2, 6);
x_24 = lean_ctor_get(x_2, 7);
x_25 = lean_ctor_get(x_2, 8);
x_26 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_27 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_29 = lean_ctor_get(x_2, 9);
lean_inc(x_29);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_30 = l_Lean_Elab_replaceRef(x_1, x_29);
lean_dec(x_29);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_31, 2, x_19);
lean_ctor_set(x_31, 3, x_20);
lean_ctor_set(x_31, 4, x_21);
lean_ctor_set(x_31, 5, x_22);
lean_ctor_set(x_31, 6, x_23);
lean_ctor_set(x_31, 7, x_24);
lean_ctor_set(x_31, 8, x_25);
lean_ctor_set(x_31, 9, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*10, x_26);
lean_ctor_set_uint8(x_31, sizeof(void*)*10 + 1, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*10 + 2, x_28);
x_32 = l_Lean_Elab_Term_ensureType(x_11, x_31, x_12);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_10);
if (x_33 == 0)
{
return x_10;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_10, 0);
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_10);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_Elab_Term_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Elab_Term_getEnv___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_add_decl(x_5, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Elab_Term_getOptions(x_2, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_KernelException_toMessageData(x_8, x_10);
x_13 = l_Lean_Elab_Term_throwError___rarg(x_12, x_2, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = l_Lean_Elab_Term_setEnv(x_14, x_2, x_6);
lean_dec(x_2);
return x_15;
}
}
}
lean_object* l_Lean_Elab_Term_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_addDecl(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_compileDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Elab_Term_getEnv___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_Term_getOptions(x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_compile_decl(x_5, x_8, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_KernelException_toMessageData(x_11, x_8);
x_13 = l_Lean_Elab_Term_throwError___rarg(x_12, x_2, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_Elab_Term_setEnv(x_14, x_2, x_9);
lean_dec(x_2);
return x_15;
}
}
}
lean_object* l_Lean_Elab_Term_compileDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_compileDecl(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_mkAuxDefinition(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_7 = l_Lean_Elab_Term_getEnv___rarg(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Term_getOptions(x_5, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Term_getMCtx___rarg(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_getLCtx(x_5, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_mkAuxDefinition(x_8, x_11, x_14, x_17, x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_KernelException_toMessageData(x_20, x_11);
x_22 = l_Lean_Elab_Term_throwError___rarg(x_21, x_5, x_18);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_11);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_Lean_Elab_Term_setEnv(x_26, x_5, x_18);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Elab_Term_setMCtx(x_27, x_5, x_29);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_25);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
lean_object* l_Lean_Elab_Term_mkAuxDefinition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Elab_Term_mkAuxDefinition(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Term_16__mkAuxNameAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_appendIndexAfter(x_2, x_3);
lean_inc(x_1);
x_5 = l_Lean_Environment_contains(x_1, x_4);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
lean_dec(x_3);
x_3 = x_7;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_Term_16__mkAuxNameAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Term_16__mkAuxNameAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_mkAuxName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("auxiliary declaration cannot be created when declaration name is not available");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_mkAuxName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_mkAuxName___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkAuxName___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_mkAuxName___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_mkAuxName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_getEnv___rarg(x_3);
x_5 = lean_ctor_get(x_2, 4);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_Term_mkAuxName___closed__3;
x_8 = l_Lean_Elab_Term_throwError___rarg(x_7, x_2, x_6);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = l_Lean_Name_append___main(x_11, x_1);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l___private_Lean_Elab_Term_16__mkAuxNameAux___main(x_10, x_12, x_13);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
lean_dec(x_5);
x_18 = l_Lean_Name_append___main(x_17, x_1);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = l___private_Lean_Elab_Term_16__mkAuxNameAux___main(x_15, x_18, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabProp___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_getAppArgs___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabProp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabProp___rarg), 1, 0);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabProp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_elabProp(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabProp___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabProp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_prop___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabProp___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Term_17__elabOptLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Syntax_isNone(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Elab_Term_elabLevel(x_6, x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_levelZero;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_Term_17__elabOptLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Term_17__elabOptLevel(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabSort(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l___private_Lean_Elab_Term_17__elabOptLevel(x_6, x_3, x_4);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_mkSort(x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = l_Lean_mkSort(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabSort___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabSort(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSort___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSort___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabSort(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_sort___elambda__1___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_elabSort___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabTypeStx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l___private_Lean_Elab_Term_17__elabOptLevel(x_6, x_3, x_4);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_mkLevelSucc(x_9);
x_11 = l_Lean_mkSort(x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = l_Lean_mkLevelSucc(x_12);
x_15 = l_Lean_mkSort(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabTypeStx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabTypeStx(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTypeStx___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_type___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabHole___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 0;
x_5 = lean_box(0);
x_6 = l_Lean_Elab_Term_mkFreshExprMVar(x_1, x_4, x_5, x_2, x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_elabHole(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabHole___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabHole___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_elabHole(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabHole___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabHole___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabHole(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_mkHole___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabHole___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabNamedHole(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getIdAt(x_1, x_5);
x_7 = 2;
x_8 = l_Lean_Elab_Term_mkFreshExprMVar(x_2, x_7, x_6, x_3, x_4);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_elabNamedHole___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabNamedHole(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNamedHole___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNamedHole___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedHole(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_namedHole___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabNamedHole___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_mkTacticMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("main");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_mkTacticMVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_mkTacticMVar___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_mkTacticMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = 2;
x_7 = l_Lean_Elab_Term_mkTacticMVar___closed__2;
lean_inc(x_3);
x_8 = l_Lean_Elab_Term_mkFreshExprMVar(x_5, x_6, x_7, x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_mvarId_x21(x_9);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_2);
x_13 = l_Lean_Elab_Term_registerSyntheticMVar(x_11, x_12, x_3, x_10);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_9);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
lean_object* _init_l_Lean_Elab_Term_elabTacticBlock___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid tactic block, expected type has not been provided");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabTacticBlock___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabTacticBlock___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabTacticBlock___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabTacticBlock___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabTacticBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_Term_elabTacticBlock___closed__3;
x_6 = l_Lean_Elab_Term_throwError___rarg(x_5, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Elab_Term_mkTacticMVar(x_7, x_9, x_3, x_4);
return x_10;
}
}
}
lean_object* l_Lean_Elab_Term_elabTacticBlock___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabTacticBlock(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabTacticBlock___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTacticBlock___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabTacticBlock(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabTacticBlock___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_elabByTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'by' tactic, expected type has not been provided");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabByTactic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabByTactic___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabByTactic___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabByTactic___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabByTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_Term_elabByTactic___closed__3;
x_6 = l_Lean_Elab_Term_throwError___rarg(x_5, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Elab_Term_mkTacticMVar(x_7, x_9, x_3, x_4);
return x_10;
}
}
}
lean_object* l_Lean_Elab_Term_elabByTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabByTactic(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabByTactic___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_byTactic___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Prod.mk");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_prodToExpr___rarg___lambda__1___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Term_18__mkPairsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
lean_dec(x_2);
x_11 = l_Lean_Syntax_inhabited;
x_12 = lean_array_get(x_11, x_1, x_10);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = l_Lean_prodToExpr___rarg___lambda__1___closed__4;
x_16 = l_Lean_addMacroScope(x_14, x_15, x_13);
x_17 = l_Lean_SourceInfo_inhabited___closed__1;
x_18 = l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__3;
x_19 = l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__5;
x_20 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_20, 3, x_19);
x_21 = l_Array_empty___closed__1;
x_22 = lean_array_push(x_21, x_20);
x_23 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_24 = lean_array_push(x_22, x_23);
x_25 = l_Lean_mkTermIdFromIdent___closed__2;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_array_push(x_21, x_26);
x_28 = lean_array_push(x_21, x_12);
x_29 = lean_array_push(x_28, x_3);
x_30 = l_Lean_nullKind___closed__2;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_array_push(x_27, x_31);
x_33 = l_Lean_mkAppStx___closed__8;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_2 = x_10;
x_3 = x_34;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_Term_18__mkPairsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Term_18__mkPairsAux___main(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Term_18__mkPairsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Term_18__mkPairsAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Term_18__mkPairsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Term_18__mkPairsAux(x_1, x_2, x_3, x_4, x_5);
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
x_8 = l___private_Lean_Elab_Term_18__mkPairsAux___main(x_1, x_6, x_7, x_2, x_3);
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
lean_object* l___private_Lean_Elab_Term_19__elabCDot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_35 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Term_getEnv___rarg(x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_39, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_39, 5);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 4);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_environment_main_module(x_40);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_36);
lean_ctor_set(x_51, 2, x_48);
lean_ctor_set(x_51, 3, x_49);
lean_inc(x_1);
x_52 = l_Lean_Elab_Term_expandCDot_x3f(x_1, x_51, x_46);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_39);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_39, 5);
lean_dec(x_54);
x_55 = lean_ctor_get(x_39, 4);
lean_dec(x_55);
x_56 = lean_ctor_get(x_39, 3);
lean_dec(x_56);
x_57 = lean_ctor_get(x_39, 2);
lean_dec(x_57);
x_58 = lean_ctor_get(x_39, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_39, 0);
lean_dec(x_59);
x_60 = lean_ctor_get(x_52, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_dec(x_52);
lean_ctor_set(x_39, 5, x_61);
x_5 = x_60;
x_6 = x_39;
goto block_34;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_39);
x_62 = lean_ctor_get(x_52, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_52, 1);
lean_inc(x_63);
lean_dec(x_52);
x_64 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_64, 0, x_41);
lean_ctor_set(x_64, 1, x_42);
lean_ctor_set(x_64, 2, x_43);
lean_ctor_set(x_64, 3, x_44);
lean_ctor_set(x_64, 4, x_45);
lean_ctor_set(x_64, 5, x_63);
x_5 = x_62;
x_6 = x_64;
goto block_34;
}
}
else
{
lean_object* x_65; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_ctor_get(x_52, 0);
lean_inc(x_65);
lean_dec(x_52);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Lean_Elab_Term_throwErrorAt___rarg(x_66, x_69, x_3, x_39);
lean_dec(x_66);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
return x_70;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_70);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
else
{
lean_object* x_75; uint8_t x_76; 
lean_dec(x_3);
x_75 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_39);
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
}
block_34:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
x_8 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_7, x_3, x_6);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_3, 7);
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_3, 7, x_13);
x_14 = 1;
x_15 = l_Lean_Elab_Term_elabTerm(x_9, x_2, x_14, x_3, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_3, 2);
x_19 = lean_ctor_get(x_3, 3);
x_20 = lean_ctor_get(x_3, 4);
x_21 = lean_ctor_get(x_3, 5);
x_22 = lean_ctor_get(x_3, 6);
x_23 = lean_ctor_get(x_3, 7);
x_24 = lean_ctor_get(x_3, 8);
x_25 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_28 = lean_ctor_get(x_3, 9);
lean_inc(x_28);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
lean_inc(x_9);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_9);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
x_31 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_17);
lean_ctor_set(x_31, 2, x_18);
lean_ctor_set(x_31, 3, x_19);
lean_ctor_set(x_31, 4, x_20);
lean_ctor_set(x_31, 5, x_21);
lean_ctor_set(x_31, 6, x_22);
lean_ctor_set(x_31, 7, x_30);
lean_ctor_set(x_31, 8, x_24);
lean_ctor_set(x_31, 9, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*10, x_25);
lean_ctor_set_uint8(x_31, sizeof(void*)*10 + 1, x_26);
lean_ctor_set_uint8(x_31, sizeof(void*)*10 + 2, x_27);
x_32 = 1;
x_33 = l_Lean_Elab_Term_elabTerm(x_9, x_2, x_32, x_31, x_6);
return x_33;
}
}
}
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_array_push(x_4, x_7);
x_9 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_9;
x_4 = x_8;
goto _start;
}
}
}
lean_object* _init_l_Lean_Elab_Term_elabParen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected parentheses notation");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabParen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabParen___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabParen___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabParen___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabParen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_32; lean_object* x_149; uint8_t x_150; 
x_149 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
lean_inc(x_1);
x_150 = l_Lean_Syntax_isOfKind(x_1, x_149);
if (x_150 == 0)
{
uint8_t x_151; 
x_151 = 0;
x_32 = x_151;
goto block_148;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_152 = l_Lean_Syntax_getArgs(x_1);
x_153 = lean_array_get_size(x_152);
lean_dec(x_152);
x_154 = lean_unsigned_to_nat(3u);
x_155 = lean_nat_dec_eq(x_153, x_154);
lean_dec(x_153);
x_32 = x_155;
goto block_148;
}
block_31:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 7);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_5);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_3, 7, x_10);
x_11 = 1;
x_12 = l_Lean_Elab_Term_elabTerm(x_5, x_2, x_11, x_3, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_ctor_get(x_3, 6);
x_20 = lean_ctor_get(x_3, 7);
x_21 = lean_ctor_get(x_3, 8);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_25 = lean_ctor_get(x_3, 9);
lean_inc(x_25);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_5);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
x_28 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_14);
lean_ctor_set(x_28, 2, x_15);
lean_ctor_set(x_28, 3, x_16);
lean_ctor_set(x_28, 4, x_17);
lean_ctor_set(x_28, 5, x_18);
lean_ctor_set(x_28, 6, x_19);
lean_ctor_set(x_28, 7, x_27);
lean_ctor_set(x_28, 8, x_21);
lean_ctor_set(x_28, 9, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*10, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*10 + 1, x_23);
lean_ctor_set_uint8(x_28, sizeof(void*)*10 + 2, x_24);
x_29 = 1;
x_30 = l_Lean_Elab_Term_elabTerm(x_5, x_2, x_29, x_28, x_6);
return x_30;
}
}
block_148:
{
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_33 = l_Lean_Elab_Term_elabParen___closed__3;
x_34 = l_Lean_Elab_Term_throwError___rarg(x_33, x_3, x_4);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_137; uint8_t x_138; 
x_35 = lean_unsigned_to_nat(1u);
x_36 = l_Lean_Syntax_getArg(x_1, x_35);
x_137 = l_Lean_nullKind___closed__2;
lean_inc(x_36);
x_138 = l_Lean_Syntax_isOfKind(x_36, x_137);
if (x_138 == 0)
{
uint8_t x_139; 
x_139 = 0;
x_37 = x_139;
goto block_136;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_140 = l_Lean_Syntax_getArgs(x_36);
x_141 = lean_array_get_size(x_140);
lean_dec(x_140);
x_142 = lean_unsigned_to_nat(0u);
x_143 = lean_nat_dec_eq(x_141, x_142);
if (x_143 == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_unsigned_to_nat(2u);
x_145 = lean_nat_dec_eq(x_141, x_144);
lean_dec(x_141);
x_37 = x_145;
goto block_136;
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_141);
lean_dec(x_36);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_146 = l_Lean_unitToExpr___lambda__1___closed__3;
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_4);
return x_147;
}
}
block_136:
{
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
x_38 = l_Lean_Elab_Term_elabParen___closed__3;
x_39 = l_Lean_Elab_Term_throwError___rarg(x_38, x_3, x_4);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; 
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Lean_Syntax_getArg(x_36, x_40);
x_42 = l_Lean_Syntax_getArg(x_36, x_35);
lean_dec(x_36);
x_43 = l_Lean_nullKind___closed__2;
lean_inc(x_42);
x_44 = l_Lean_Syntax_isOfKind(x_42, x_43);
if (x_44 == 0)
{
uint8_t x_132; 
x_132 = 0;
x_45 = x_132;
goto block_131;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = l_Lean_Syntax_getArgs(x_42);
x_134 = lean_array_get_size(x_133);
lean_dec(x_133);
x_135 = lean_nat_dec_eq(x_134, x_35);
lean_dec(x_134);
x_45 = x_135;
goto block_131;
}
block_131:
{
if (x_45 == 0)
{
lean_dec(x_1);
if (x_44 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_2);
x_46 = l_Lean_Elab_Term_elabParen___closed__3;
x_47 = l_Lean_Elab_Term_throwError___rarg(x_46, x_3, x_4);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = l_Lean_Syntax_getArgs(x_42);
lean_dec(x_42);
x_49 = lean_array_get_size(x_48);
lean_dec(x_48);
x_50 = lean_nat_dec_eq(x_49, x_40);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_41);
lean_dec(x_2);
x_51 = l_Lean_Elab_Term_elabParen___closed__3;
x_52 = l_Lean_Elab_Term_throwError___rarg(x_51, x_3, x_4);
return x_52;
}
else
{
lean_object* x_53; 
x_53 = l___private_Lean_Elab_Term_19__elabCDot(x_41, x_2, x_3, x_4);
return x_53;
}
}
}
else
{
lean_object* x_54; uint8_t x_55; lean_object* x_98; uint8_t x_99; 
x_54 = l_Lean_Syntax_getArg(x_42, x_40);
lean_dec(x_42);
x_98 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__2;
lean_inc(x_54);
x_99 = l_Lean_Syntax_isOfKind(x_54, x_98);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = l_Lean_Parser_Term_tupleTail___elambda__1___closed__2;
lean_inc(x_54);
x_101 = l_Lean_Syntax_isOfKind(x_54, x_100);
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = 0;
x_55 = x_102;
goto block_97;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_103 = l_Lean_Syntax_getArgs(x_54);
x_104 = lean_array_get_size(x_103);
lean_dec(x_103);
x_105 = lean_unsigned_to_nat(2u);
x_106 = lean_nat_dec_eq(x_104, x_105);
lean_dec(x_104);
x_55 = x_106;
goto block_97;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = l_Lean_Syntax_getArgs(x_54);
x_108 = lean_array_get_size(x_107);
lean_dec(x_107);
x_109 = lean_unsigned_to_nat(2u);
x_110 = lean_nat_dec_eq(x_108, x_109);
lean_dec(x_108);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = l_Lean_Parser_Term_tupleTail___elambda__1___closed__2;
lean_inc(x_54);
x_112 = l_Lean_Syntax_isOfKind(x_54, x_111);
if (x_112 == 0)
{
uint8_t x_113; 
x_113 = 0;
x_55 = x_113;
goto block_97;
}
else
{
x_55 = x_110;
goto block_97;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_2);
lean_dec(x_1);
x_114 = l_Lean_Syntax_getArg(x_54, x_35);
lean_dec(x_54);
lean_inc(x_3);
x_115 = l_Lean_Elab_Term_elabType(x_114, x_3, x_4);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_116);
lean_inc(x_3);
lean_inc(x_118);
x_119 = l___private_Lean_Elab_Term_19__elabCDot(x_41, x_118, x_3, x_117);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = l_Lean_Elab_Term_ensureHasType(x_118, x_120, x_3, x_121);
return x_122;
}
else
{
uint8_t x_123; 
lean_dec(x_118);
lean_dec(x_3);
x_123 = !lean_is_exclusive(x_119);
if (x_123 == 0)
{
return x_119;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_119, 0);
x_125 = lean_ctor_get(x_119, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_119);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_41);
lean_dec(x_3);
x_127 = !lean_is_exclusive(x_115);
if (x_127 == 0)
{
return x_115;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_115, 0);
x_129 = lean_ctor_get(x_115, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_115);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
block_97:
{
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_41);
lean_dec(x_2);
lean_dec(x_1);
x_56 = l_Lean_Elab_Term_elabParen___closed__3;
x_57 = l_Lean_Elab_Term_throwError___rarg(x_56, x_3, x_4);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_58 = l_Lean_Syntax_getArg(x_54, x_35);
lean_dec(x_54);
x_59 = l_Lean_Syntax_getArgs(x_58);
lean_dec(x_58);
x_60 = l_Lean_mkOptionalNode___closed__2;
x_61 = lean_array_push(x_60, x_41);
x_62 = lean_unsigned_to_nat(2u);
x_63 = l_Array_empty___closed__1;
x_64 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_62, x_59, x_40, x_63);
lean_dec(x_59);
x_65 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_64, x_64, x_40, x_61);
lean_dec(x_64);
x_66 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Elab_Term_getEnv___rarg(x_68);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_73 = lean_ctor_get(x_70, 5);
x_74 = lean_ctor_get(x_3, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_74, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 4);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_environment_main_module(x_71);
x_78 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_67);
lean_ctor_set(x_78, 2, x_75);
lean_ctor_set(x_78, 3, x_76);
x_79 = l_Lean_Elab_Term_mkPairs(x_65, x_78, x_73);
lean_dec(x_65);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_ctor_set(x_70, 5, x_81);
x_5 = x_80;
x_6 = x_70;
goto block_31;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_82 = lean_ctor_get(x_70, 0);
x_83 = lean_ctor_get(x_70, 1);
x_84 = lean_ctor_get(x_70, 2);
x_85 = lean_ctor_get(x_70, 3);
x_86 = lean_ctor_get(x_70, 4);
x_87 = lean_ctor_get(x_70, 5);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_70);
x_88 = lean_ctor_get(x_3, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_88, 3);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 4);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_environment_main_module(x_71);
x_92 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_67);
lean_ctor_set(x_92, 2, x_89);
lean_ctor_set(x_92, 3, x_90);
x_93 = l_Lean_Elab_Term_mkPairs(x_65, x_92, x_87);
lean_dec(x_65);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_96, 0, x_82);
lean_ctor_set(x_96, 1, x_83);
lean_ctor_set(x_96, 2, x_84);
lean_ctor_set(x_96, 3, x_85);
lean_ctor_set(x_96, 4, x_86);
lean_ctor_set(x_96, 5, x_95);
x_5 = x_94;
x_6 = x_96;
goto block_31;
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
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabParen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabParen), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabParen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabParen___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_expandListLit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = lean_array_fget(x_3, x_10);
x_12 = l_Lean_mkAppStx___closed__9;
x_13 = lean_array_push(x_12, x_11);
x_14 = lean_array_push(x_13, x_6);
lean_inc(x_2);
x_15 = l_Lean_mkAppStx(x_2, x_14);
x_4 = x_10;
x_5 = lean_box(0);
x_6 = x_15;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
}
lean_object* l_Lean_Elab_Term_expandListLit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_listToExpr___rarg___closed__6;
x_11 = l_Lean_mkTermIdFrom(x_5, x_10);
lean_dec(x_5);
x_12 = l_Lean_listToExpr___rarg___closed__4;
x_13 = l_Lean_mkTermIdFrom(x_9, x_12);
lean_dec(x_9);
x_14 = l_Lean_Syntax_getArgs(x_7);
lean_dec(x_7);
x_15 = l_Array_empty___closed__1;
x_16 = l_Array_foldlStepMAux___main___at_Lean_Syntax_foldSepRevArgsM___spec__1(x_8, x_14, x_4, x_15);
lean_dec(x_14);
x_17 = lean_array_get_size(x_16);
x_18 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_expandListLit___spec__1(x_1, x_11, x_16, x_17, lean_box(0), x_13);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_expandListLit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_expandListLit___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_expandListLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandListLit(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandListLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandListLit___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandListLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_Lean_Parser_Term_listLit___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandListLit___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_expandArrayLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected array literal syntax");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_expandArrayLit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("List.toArray");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_expandArrayLit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_expandArrayLit___closed__2;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_expandArrayLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_expandArrayLit___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_expandArrayLit___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_expandArrayLit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_arrayToExpr___rarg___lambda__1___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_expandArrayLit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_expandArrayLit___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_expandArrayLit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_List_repr___rarg___closed__2;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_expandArrayLit___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_expandArrayLit___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_expandArrayLit___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_List_repr___rarg___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandArrayLit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Parser_Term_arrayLit___elambda__1___closed__2;
lean_inc(x_1);
x_44 = l_Lean_Syntax_isOfKind(x_1, x_43);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = 0;
x_4 = x_45;
goto block_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = l_Lean_Syntax_getArgs(x_1);
x_47 = lean_array_get_size(x_46);
lean_dec(x_46);
x_48 = lean_unsigned_to_nat(3u);
x_49 = lean_nat_dec_eq(x_47, x_48);
lean_dec(x_47);
x_4 = x_49;
goto block_42;
}
block_42:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = l_Lean_Elab_Term_expandArrayLit___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Lean_arrayToExpr___rarg___lambda__1___closed__2;
x_14 = l_Lean_addMacroScope(x_12, x_13, x_11);
x_15 = l_Lean_SourceInfo_inhabited___closed__1;
x_16 = l_Lean_Elab_Term_expandArrayLit___closed__4;
x_17 = l_Lean_Elab_Term_expandArrayLit___closed__6;
x_18 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_17);
x_19 = l_Array_empty___closed__1;
x_20 = lean_array_push(x_19, x_18);
x_21 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_22 = lean_array_push(x_20, x_21);
x_23 = l_Lean_mkTermIdFromIdent___closed__2;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_array_push(x_19, x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_10, x_10, x_26, x_19);
lean_dec(x_10);
x_28 = l_Lean_nullKind___closed__2;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Elab_Term_expandArrayLit___closed__8;
x_31 = lean_array_push(x_30, x_29);
x_32 = l_Lean_Elab_Term_expandArrayLit___closed__9;
x_33 = lean_array_push(x_31, x_32);
x_34 = l_Lean_Parser_Term_listLit___elambda__1___closed__2;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_array_push(x_19, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_array_push(x_25, x_37);
x_39 = l_Lean_mkAppStx___closed__8;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_3);
return x_41;
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandArrayLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandArrayLit), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandArrayLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_Lean_Parser_Term_arrayLit___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_expandArrayLit___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Term_20__resolveLocalNameAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = lean_local_ctx_find_from_user_name(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
x_2 = x_5;
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
}
else
{
uint8_t x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = l_Lean_LocalDecl_toExpr(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec(x_4);
x_15 = l_Lean_LocalDecl_toExpr(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
lean_object* l___private_Lean_Elab_Term_20__resolveLocalNameAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Term_20__resolveLocalNameAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Term_21__resolveLocalName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_getLCtx(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_box(0);
x_8 = l___private_Lean_Elab_Term_20__resolveLocalNameAux___main(x_6, x_1, x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_box(0);
x_12 = l___private_Lean_Elab_Term_20__resolveLocalNameAux___main(x_9, x_1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
lean_object* l___private_Lean_Elab_Term_21__resolveLocalName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Term_21__resolveLocalName(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_isLocalTermId_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_isTermId_x3f(x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 3)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l___private_Lean_Elab_Term_21__resolveLocalName(x_10, x_3, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_11, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
lean_ctor_set(x_12, 0, x_24);
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
lean_ctor_set(x_12, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_21);
lean_free_object(x_12);
lean_dec(x_20);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_11, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_11, 0, x_30);
return x_11;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_dec(x_11);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_12, 0);
lean_inc(x_34);
lean_dec(x_12);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_37 = x_11;
} else {
 lean_dec_ref(x_11);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
if (lean_is_scalar(x_37)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_37;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_35);
lean_dec(x_34);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_42 = x_11;
} else {
 lean_dec_ref(x_11);
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
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_9);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_4);
return x_46;
}
}
}
}
lean_object* l_Lean_Elab_Term_isLocalTermId_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Elab_Term_isLocalTermId_x3f(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Term_22__mkFreshLevelMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_2);
lean_inc(x_4);
x_10 = l_Lean_Elab_Term_mkFreshLevelMVar(x_4, x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_9;
x_3 = x_13;
x_5 = x_12;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
}
lean_object* l___private_Lean_Elab_Term_22__mkFreshLevelMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
lean_inc(x_1);
x_5 = l_Nat_foldMAux___main___at___private_Lean_Elab_Term_22__mkFreshLevelMVars___spec__1(x_1, x_1, x_4, x_2, x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Term_22__mkFreshLevelMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldMAux___main___at___private_Lean_Elab_Term_22__mkFreshLevelMVars___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Term_mkConst___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toStr___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkConst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_mkConst___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkConst___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many explicit universe levels");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_mkConst___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_mkConst___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkConst___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_mkConst___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_mkConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Elab_Term_getEnv___rarg(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_1);
x_8 = lean_environment_find(x_6, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_9 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = l_Lean_Elab_Term_mkConst___closed__2;
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_Term_throwError___rarg(x_13, x_3, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = l_Lean_ConstantInfo_lparams(x_15);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_List_lengthAux___main___rarg(x_16, x_17);
lean_dec(x_16);
x_19 = l_List_lengthAux___main___rarg(x_2, x_17);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_nat_sub(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_22 = l___private_Lean_Elab_Term_22__mkFreshLevelMVars(x_21, x_3, x_7);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_List_append___rarg(x_2, x_24);
x_26 = l_Lean_mkConst(x_1, x_25);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_22);
x_29 = l_List_append___rarg(x_2, x_27);
x_30 = l_Lean_mkConst(x_1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_32 = l_Lean_Elab_Term_mkConst___closed__5;
x_33 = l_Lean_Elab_Term_throwError___rarg(x_32, x_3, x_7);
return x_33;
}
}
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Term_23__mkConsts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_4);
lean_inc(x_1);
x_13 = l_Lean_Elab_Term_mkConst(x_11, x_1, x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_8, 0, x_14);
lean_ctor_set(x_3, 1, x_2);
x_2 = x_3;
x_3 = x_10;
x_5 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_free_object(x_8);
lean_dec(x_12);
lean_free_object(x_3);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_3, 1);
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
lean_inc(x_4);
lean_inc(x_1);
x_24 = l_Lean_Elab_Term_mkConst(x_22, x_1, x_4, x_5);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_27);
x_2 = x_3;
x_3 = x_21;
x_5 = x_26;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_23);
lean_free_object(x_3);
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_31 = x_24;
} else {
 lean_dec_ref(x_24);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_3, 0);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_3);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_37 = x_33;
} else {
 lean_dec_ref(x_33);
 x_37 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_1);
x_38 = l_Lean_Elab_Term_mkConst(x_35, x_1, x_4, x_5);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
if (lean_is_scalar(x_37)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_37;
}
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_36);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_2);
x_2 = x_42;
x_3 = x_34;
x_5 = x_40;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_46 = x_38;
} else {
 lean_dec_ref(x_38);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Term_23__mkConsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Elab_Term_getEnv___rarg(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = l_List_foldlM___main___at___private_Lean_Elab_Term_23__mkConsts___spec__1(x_2, x_7, x_1, x_3, x_6);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_resolveGlobalName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lean_Elab_Term_getEnv___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_Term_getCurrNamespace(x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Term_getOpenDecls(x_2, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Elab_resolveGlobalName(x_5, x_8, x_12, x_1);
lean_dec(x_8);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l_Lean_Elab_resolveGlobalName(x_5, x_8, x_14, x_1);
lean_dec(x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
lean_object* l_Lean_Elab_Term_resolveGlobalName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_resolveGlobalName(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown identifier '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_resolveName___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_resolveName___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of explicit universe parameters, '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_resolveName___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_resolveName___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is a local");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_resolveName___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_resolveName___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_resolveName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_6 = l___private_Lean_Elab_Term_21__resolveLocalName(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_List_isEmpty___rarg(x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l___private_Lean_Elab_Term_23__mkConsts(x_2, x_3, x_4, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_2);
lean_inc(x_1);
x_11 = l_Lean_Elab_Term_resolveGlobalName(x_1, x_4, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_List_isEmpty___rarg(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = l___private_Lean_Elab_Term_23__mkConsts(x_12, x_3, x_4, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_3);
x_16 = l_Lean_Elab_Term_getMainModule___rarg(x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_extractMacroScopes(x_1);
x_20 = l_Lean_MacroScopesView_format(x_19, x_17);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_Elab_Term_resolveName___closed__3;
x_23 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_25 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Elab_Term_throwError___rarg(x_25, x_4, x_18);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
else
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_ctor_get(x_7, 0);
lean_inc(x_31);
lean_dec(x_7);
x_32 = !lean_is_exclusive(x_6);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_6, 1);
x_34 = lean_ctor_get(x_6, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
x_36 = l_List_isEmpty___rarg(x_3);
lean_dec(x_3);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_37);
if (x_36 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_38);
lean_free_object(x_6);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_35);
x_40 = l_Lean_Elab_Term_resolveName___closed__6;
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Elab_Term_resolveName___closed__9;
x_43 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Elab_Term_throwError___rarg(x_43, x_4, x_33);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
lean_dec(x_35);
lean_dec(x_4);
lean_ctor_set(x_6, 0, x_38);
return x_6;
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_6, 1);
lean_inc(x_49);
lean_dec(x_6);
x_50 = lean_ctor_get(x_31, 0);
lean_inc(x_50);
x_51 = l_List_isEmpty___rarg(x_3);
lean_dec(x_3);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_31);
lean_ctor_set(x_53, 1, x_52);
if (x_51 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_53);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_50);
x_55 = l_Lean_Elab_Term_resolveName___closed__6;
x_56 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Elab_Term_resolveName___closed__9;
x_58 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Elab_Term_throwError___rarg(x_58, x_4, x_49);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
else
{
lean_object* x_64; 
lean_dec(x_50);
lean_dec(x_4);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_49);
return x_64;
}
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_elabBadCDot___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabBadCDot___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabBadCDot___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabBadCDot___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabBadCDot___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabBadCDot___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Term_elabBadCDot___rarg___closed__3;
x_4 = l_Lean_Elab_Term_throwError___rarg(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabBadCDot(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBadCDot___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabBadCDot___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_elabBadCDot(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBadCDot___boxed), 2, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabBadCDot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_cdot___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_elabRawStrLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed syntax");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabRawStrLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabRawStrLit___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabRawStrLit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabRawStrLit___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabRawStrLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_isStrLit_x3f(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Elab_Term_elabRawStrLit___closed__3;
x_7 = l_Lean_Elab_Term_throwError___rarg(x_6, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_mkStrLit(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
lean_object* l_Lean_Elab_Term_elabRawStrLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabRawStrLit(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabRawStrLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabRawStrLit___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabRawStrLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_strLitKind___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabRawStrLit___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabStr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Elab_Term_elabRawStrLit(x_6, x_2, x_3, x_4);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabStr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabStr(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabStr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabStr___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabStr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_String_HasQuote___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabStr___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_elabRawNumLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Literal_type___closed__3;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabRawNumLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_62; lean_object* x_63; 
x_62 = l_Lean_numLitKind;
x_63 = l_Lean_Syntax_isNatLitAux(x_62, x_1);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_2);
x_64 = l_Lean_Elab_Term_elabRawStrLit___closed__3;
x_65 = l_Lean_Elab_Term_throwError___rarg(x_64, x_3, x_4);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
return x_65;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_65);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_63, 0);
lean_inc(x_70);
lean_dec(x_63);
x_71 = l_Lean_mkNatLit(x_70);
x_5 = x_71;
x_6 = x_4;
goto block_61;
}
block_61:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_50; lean_object* x_51; 
x_7 = 1;
x_8 = lean_box(0);
lean_inc(x_3);
x_9 = l_Lean_Elab_Term_mkFreshTypeMVar(x_7, x_8, x_3, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_mvarId_x21(x_10);
x_13 = lean_box(0);
x_50 = l_Lean_Elab_Term_elabRawNumLit___closed__1;
x_51 = l_Lean_Elab_Term_registerSyntheticMVar(x_12, x_50, x_3, x_11);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_14 = x_52;
goto block_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_10);
x_55 = l_Lean_Elab_Term_isDefEq(x_54, x_10, x_3, x_53);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_14 = x_56;
goto block_49;
}
else
{
uint8_t x_57; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_55);
if (x_57 == 0)
{
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_55, 0);
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_55);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
block_49:
{
lean_object* x_15; 
lean_inc(x_3);
lean_inc(x_10);
x_15 = l_Lean_Elab_Term_getLevel(x_10, x_3, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
x_18 = l_Lean_Elab_Term_decLevel(x_16, x_3, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_13);
x_22 = l_Lean_Meta_evalNat___main___closed__7;
lean_inc(x_21);
x_23 = l_Lean_mkConst(x_22, x_21);
lean_inc(x_10);
x_24 = l_Lean_mkApp(x_23, x_10);
x_25 = l_Lean_Elab_Term_mkInstMVar(x_24, x_3, x_20);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = l_Lean_Meta_evalNat___main___closed__8;
x_29 = l_Lean_mkConst(x_28, x_21);
x_30 = l_Lean_mkApp3(x_29, x_10, x_27, x_5);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = l_Lean_Meta_evalNat___main___closed__8;
x_34 = l_Lean_mkConst(x_33, x_21);
x_35 = l_Lean_mkApp3(x_34, x_10, x_31, x_5);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_5);
x_37 = !lean_is_exclusive(x_25);
if (x_37 == 0)
{
return x_25;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_25, 0);
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_25);
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
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_18);
if (x_41 == 0)
{
return x_18;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_18, 0);
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_18);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_15);
if (x_45 == 0)
{
return x_15;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_15, 0);
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_15);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_elabRawNumLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabRawNumLit(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabRawNumLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabRawNumLit___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabRawNumLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_numLitKind___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabRawNumLit___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabNum(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Elab_Term_elabRawNumLit(x_6, x_2, x_3, x_4);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabNum___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabNum(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNum___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNum___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabNum(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Nat_HasQuote___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabNum___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabRawCharLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_isCharLit_x3f(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Elab_Term_elabRawStrLit___closed__3;
x_7 = l_Lean_Elab_Term_throwError___rarg(x_6, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_unbox_uint32(x_8);
lean_dec(x_8);
x_10 = lean_uint32_to_nat(x_9);
x_11 = l_Lean_mkNatLit(x_10);
x_12 = l_Lean_charToExpr___lambda__1___closed__1;
x_13 = l_Lean_mkApp(x_12, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
}
}
lean_object* l_Lean_Elab_Term_elabRawCharLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabRawCharLit(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabRawCharLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabRawCharLit___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabRawCharLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_charLitKind___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabRawCharLit___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabChar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Elab_Term_elabRawCharLit(x_6, x_2, x_3, x_4);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabChar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabChar(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabChar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabChar___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabChar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_char___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabChar___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabQuotedName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_isNameLit_x3f(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Elab_Term_elabRawStrLit___closed__3;
x_9 = l_Lean_Elab_Term_throwError___rarg(x_8, x_3, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Name_toExprAux___main(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
}
lean_object* l_Lean_Elab_Term_elabQuotedName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabQuotedName(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabQuotedName___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabQuotedName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_quotedName___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_MetaHasEval___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Message_toString(x_1);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_IO_println___at_IO_runMeta___spec__1(x_4, x_2);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_MetaHasEval___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<TermElabM>");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_MetaHasEval___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_MetaHasEval___rarg___lambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_MetaHasEval___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("error: unsupported syntax");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_MetaHasEval___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_MetaHasEval___rarg___closed__3;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_MetaHasEval___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("error: elaborator postponed");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_MetaHasEval___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_MetaHasEval___rarg___closed__5;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_MetaHasEval___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_7 = 0;
x_8 = 1;
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 1, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 2, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 3, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 4, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 5, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 6, x_8);
x_10 = l_Lean_getMaxRecDepth(x_3);
x_11 = l_Lean_LocalContext_Inhabited___closed__2;
x_12 = l_Array_empty___closed__1;
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_14, 4, x_10);
x_15 = lean_box(0);
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Term_MetaHasEval___rarg___closed__1;
x_18 = l_Lean_FileMap_Inhabited___closed__1;
x_19 = lean_box(0);
x_20 = l_Lean_firstFrontendMacroScope;
x_21 = 1;
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_15);
lean_ctor_set(x_23, 5, x_16);
lean_ctor_set(x_23, 6, x_16);
lean_ctor_set(x_23, 7, x_16);
lean_ctor_set(x_23, 8, x_20);
lean_ctor_set(x_23, 9, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*10, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*10 + 1, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*10 + 2, x_21);
x_24 = l_Lean_MetavarContext_Inhabited___closed__1;
x_25 = l_Lean_Meta_run___rarg___closed__5;
x_26 = l_Lean_NameGenerator_Inhabited___closed__3;
x_27 = l_Lean_TraceState_Inhabited___closed__1;
x_28 = l_Std_PersistentArray_empty___closed__3;
x_29 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_26);
lean_ctor_set(x_29, 4, x_27);
lean_ctor_set(x_29, 5, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = l_Lean_Unhygienic_run___rarg___closed__1;
x_32 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_16);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_30);
lean_ctor_set(x_32, 4, x_30);
lean_ctor_set(x_32, 5, x_31);
x_33 = lean_apply_2(x_4, x_23, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_35, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Elab_Term_MetaHasEval___rarg___closed__2;
x_40 = l_Std_PersistentArray_forM___at___private_Lean_Parser_Module_4__testModuleParserAux___main___spec__6(x_39, x_36, x_6);
lean_dec(x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(x_21);
x_43 = lean_apply_5(x_1, x_38, x_3, x_34, x_42, x_41);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_3);
lean_dec(x_1);
x_48 = lean_ctor_get(x_33, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_33, 1);
lean_inc(x_50);
lean_dec(x_33);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 2);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Message_toString(x_51);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_Options_empty;
x_56 = l_Lean_Format_pretty(x_54, x_55);
x_57 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Lean_Elab_Term_MetaHasEval___rarg___closed__2;
x_59 = l_Std_PersistentArray_forM___at___private_Lean_Parser_Module_4__testModuleParserAux___main___spec__6(x_58, x_52, x_6);
lean_dec(x_52);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
lean_ctor_set_tag(x_59, 1);
lean_ctor_set(x_59, 0, x_57);
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_57);
x_64 = !lean_is_exclusive(x_59);
if (x_64 == 0)
{
return x_59;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_59, 0);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_59);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_33, 1);
lean_inc(x_68);
lean_dec(x_33);
x_69 = lean_ctor_get(x_68, 2);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Lean_Elab_Term_MetaHasEval___rarg___closed__2;
x_71 = l_Std_PersistentArray_forM___at___private_Lean_Parser_Module_4__testModuleParserAux___main___spec__6(x_70, x_69, x_6);
lean_dec(x_69);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
x_74 = l_Lean_Elab_Term_MetaHasEval___rarg___closed__4;
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 0, x_74);
return x_71;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = l_Lean_Elab_Term_MetaHasEval___rarg___closed__4;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_71);
if (x_78 == 0)
{
return x_71;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_71, 0);
x_80 = lean_ctor_get(x_71, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_71);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_33, 1);
lean_inc(x_82);
lean_dec(x_33);
x_83 = lean_ctor_get(x_82, 2);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_Lean_Elab_Term_MetaHasEval___rarg___closed__2;
x_85 = l_Std_PersistentArray_forM___at___private_Lean_Parser_Module_4__testModuleParserAux___main___spec__6(x_84, x_83, x_6);
lean_dec(x_83);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
x_88 = l_Lean_Elab_Term_MetaHasEval___rarg___closed__6;
lean_ctor_set_tag(x_85, 1);
lean_ctor_set(x_85, 0, x_88);
return x_85;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
lean_dec(x_85);
x_90 = l_Lean_Elab_Term_MetaHasEval___rarg___closed__6;
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_85);
if (x_92 == 0)
{
return x_85;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_85, 0);
x_94 = lean_ctor_get(x_85, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_85);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_MetaHasEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_MetaHasEval___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_MetaHasEval___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_Lean_Elab_Term_MetaHasEval___rarg(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
lean_object* _init_l___private_Lean_Elab_Term_24__regTraceClasses___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l_Lean_Elab_Term_tryCoe___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Term_24__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Term_10__postponeElabTerm___closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l___private_Lean_Elab_Term_24__regTraceClasses___closed__1;
x_6 = l_Lean_registerTraceClass(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Elab_Term_logDbgTrace___closed__1;
x_9 = l_Lean_registerTraceClass(x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
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
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
return x_6;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
return x_3;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_Sorry(lean_object*);
lean_object* initialize_Lean_Structure(lean_object*);
lean_object* initialize_Lean_Meta_ExprDefEq(lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(lean_object*);
lean_object* initialize_Lean_Hygiene(lean_object*);
lean_object* initialize_Lean_Util_RecDepth(lean_object*);
lean_object* initialize_Lean_Elab_Log(lean_object*);
lean_object* initialize_Lean_Elab_Alias(lean_object*);
lean_object* initialize_Lean_Elab_ResolveName(lean_object*);
lean_object* initialize_Lean_Elab_Level(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Term(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Sorry(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Structure(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ExprDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Hygiene(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_RecDepth(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Log(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Alias(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ResolveName(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Level(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_State_inhabited___closed__1 = _init_l_Lean_Elab_Term_State_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_State_inhabited___closed__1);
l_Lean_Elab_Term_State_inhabited___closed__2 = _init_l_Lean_Elab_Term_State_inhabited___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_State_inhabited___closed__2);
l_Lean_Elab_Term_State_inhabited = _init_l_Lean_Elab_Term_State_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_State_inhabited);
l_Lean_Elab_Term_Exception_inhabited = _init_l_Lean_Elab_Term_Exception_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_Exception_inhabited);
l_Lean_Elab_Term_TermElabResult_inhabited___closed__1 = _init_l_Lean_Elab_Term_TermElabResult_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_TermElabResult_inhabited___closed__1);
l_Lean_Elab_Term_TermElabResult_inhabited = _init_l_Lean_Elab_Term_TermElabResult_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_TermElabResult_inhabited);
l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1 = _init_l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1);
l_Lean_Elab_Term_monadLog___closed__1 = _init_l_Lean_Elab_Term_monadLog___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_monadLog___closed__1);
l_Lean_Elab_Term_monadLog___closed__2 = _init_l_Lean_Elab_Term_monadLog___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_monadLog___closed__2);
l_Lean_Elab_Term_monadLog___closed__3 = _init_l_Lean_Elab_Term_monadLog___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_monadLog___closed__3);
l_Lean_Elab_Term_monadLog___closed__4 = _init_l_Lean_Elab_Term_monadLog___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_monadLog___closed__4);
l_Lean_Elab_Term_monadLog___closed__5 = _init_l_Lean_Elab_Term_monadLog___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_monadLog___closed__5);
l_Lean_Elab_Term_monadLog___closed__6 = _init_l_Lean_Elab_Term_monadLog___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_monadLog___closed__6);
l_Lean_Elab_Term_monadLog___closed__7 = _init_l_Lean_Elab_Term_monadLog___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_monadLog___closed__7);
l_Lean_Elab_Term_monadLog___closed__8 = _init_l_Lean_Elab_Term_monadLog___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_monadLog___closed__8);
l_Lean_Elab_Term_monadLog___closed__9 = _init_l_Lean_Elab_Term_monadLog___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_monadLog___closed__9);
l_Lean_Elab_Term_monadLog___closed__10 = _init_l_Lean_Elab_Term_monadLog___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_monadLog___closed__10);
l_Lean_Elab_Term_monadLog___closed__11 = _init_l_Lean_Elab_Term_monadLog___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_monadLog___closed__11);
l_Lean_Elab_Term_monadLog = _init_l_Lean_Elab_Term_monadLog();
lean_mark_persistent(l_Lean_Elab_Term_monadLog);
l_Lean_Elab_Term_throwUnsupportedSyntax___rarg___closed__1 = _init_l_Lean_Elab_Term_throwUnsupportedSyntax___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_throwUnsupportedSyntax___rarg___closed__1);
l_Lean_Elab_Term_monadQuotation___closed__1 = _init_l_Lean_Elab_Term_monadQuotation___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_monadQuotation___closed__1);
l_Lean_Elab_Term_monadQuotation___closed__2 = _init_l_Lean_Elab_Term_monadQuotation___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_monadQuotation___closed__2);
l_Lean_Elab_Term_monadQuotation___closed__3 = _init_l_Lean_Elab_Term_monadQuotation___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_monadQuotation___closed__3);
l_Lean_Elab_Term_monadQuotation___closed__4 = _init_l_Lean_Elab_Term_monadQuotation___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_monadQuotation___closed__4);
l_Lean_Elab_Term_monadQuotation = _init_l_Lean_Elab_Term_monadQuotation();
lean_mark_persistent(l_Lean_Elab_Term_monadQuotation);
l_Lean_Elab_Term_mkTermElabAttribute___closed__1 = _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkTermElabAttribute___closed__1);
l_Lean_Elab_Term_mkTermElabAttribute___closed__2 = _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkTermElabAttribute___closed__2);
l_Lean_Elab_Term_mkTermElabAttribute___closed__3 = _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_mkTermElabAttribute___closed__3);
l_Lean_Elab_Term_mkTermElabAttribute___closed__4 = _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_mkTermElabAttribute___closed__4);
l_Lean_Elab_Term_mkTermElabAttribute___closed__5 = _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_mkTermElabAttribute___closed__5);
l_Lean_Elab_Term_mkTermElabAttribute___closed__6 = _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_mkTermElabAttribute___closed__6);
l_Lean_Elab_Term_mkTermElabAttribute___closed__7 = _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_mkTermElabAttribute___closed__7);
l_Lean_Elab_Term_mkTermElabAttribute___closed__8 = _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_mkTermElabAttribute___closed__8);
l_Lean_Elab_Term_mkTermElabAttribute___closed__9 = _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_mkTermElabAttribute___closed__9);
l_Std_PersistentHashMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__3 = _init_l_Std_PersistentHashMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__3();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__3);
l_Lean_SMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__1___closed__1 = _init_l_Lean_SMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__1___closed__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__1___closed__1);
l_Lean_SMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__1___closed__2 = _init_l_Lean_SMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__1___closed__2();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__1___closed__2);
l_Lean_SMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__1 = _init_l_Lean_SMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Term_termElabAttribute___spec__1);
l_Lean_Elab_Term_termElabAttribute___closed__1 = _init_l_Lean_Elab_Term_termElabAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_termElabAttribute___closed__1);
l_Lean_Elab_Term_termElabAttribute___closed__2 = _init_l_Lean_Elab_Term_termElabAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_termElabAttribute___closed__2);
l_Lean_Elab_Term_termElabAttribute___closed__3 = _init_l_Lean_Elab_Term_termElabAttribute___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_termElabAttribute___closed__3);
l_Lean_Elab_Term_termElabAttribute___closed__4 = _init_l_Lean_Elab_Term_termElabAttribute___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_termElabAttribute___closed__4);
l_Lean_Elab_Term_termElabAttribute___closed__5 = _init_l_Lean_Elab_Term_termElabAttribute___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_termElabAttribute___closed__5);
res = l_Lean_Elab_Term_mkTermElabAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_termElabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_termElabAttribute);
lean_dec_ref(res);
l_Lean_Elab_Term_logDbgTrace___closed__1 = _init_l_Lean_Elab_Term_logDbgTrace___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_logDbgTrace___closed__1);
l_Lean_Elab_Term_throwErrorIfErrors___closed__1 = _init_l_Lean_Elab_Term_throwErrorIfErrors___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_throwErrorIfErrors___closed__1);
l_Lean_Elab_Term_throwErrorIfErrors___closed__2 = _init_l_Lean_Elab_Term_throwErrorIfErrors___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_throwErrorIfErrors___closed__2);
l_Lean_Elab_Term_throwErrorIfErrors___closed__3 = _init_l_Lean_Elab_Term_throwErrorIfErrors___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_throwErrorIfErrors___closed__3);
l_Lean_Elab_Term_mkExplicitBinder___closed__1 = _init_l_Lean_Elab_Term_mkExplicitBinder___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkExplicitBinder___closed__1);
l_Lean_Elab_Term_mkExplicitBinder___closed__2 = _init_l_Lean_Elab_Term_mkExplicitBinder___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkExplicitBinder___closed__2);
l_Lean_Elab_Term_mkExplicitBinder___closed__3 = _init_l_Lean_Elab_Term_mkExplicitBinder___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_mkExplicitBinder___closed__3);
l_Lean_Elab_Term_mkExplicitBinder___closed__4 = _init_l_Lean_Elab_Term_mkExplicitBinder___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_mkExplicitBinder___closed__4);
l_Lean_Elab_Term_mkExplicitBinder___closed__5 = _init_l_Lean_Elab_Term_mkExplicitBinder___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_mkExplicitBinder___closed__5);
l_Lean_Elab_Term_mkExplicitBinder___closed__6 = _init_l_Lean_Elab_Term_mkExplicitBinder___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_mkExplicitBinder___closed__6);
l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__1 = _init_l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__1);
l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__2 = _init_l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__2);
l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__1 = _init_l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__1);
l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__2 = _init_l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__2);
l___private_Lean_Elab_Term_5__expandCDot___main___closed__1 = _init_l___private_Lean_Elab_Term_5__expandCDot___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Term_5__expandCDot___main___closed__1);
l___private_Lean_Elab_Term_5__expandCDot___main___closed__2 = _init_l___private_Lean_Elab_Term_5__expandCDot___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Term_5__expandCDot___main___closed__2);
l___private_Lean_Elab_Term_5__expandCDot___main___closed__3 = _init_l___private_Lean_Elab_Term_5__expandCDot___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Term_5__expandCDot___main___closed__3);
l_Lean_Elab_Term_expandCDot_x3f___closed__1 = _init_l_Lean_Elab_Term_expandCDot_x3f___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandCDot_x3f___closed__1);
l_Lean_Elab_Term_expandCDot_x3f___closed__2 = _init_l_Lean_Elab_Term_expandCDot_x3f___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandCDot_x3f___closed__2);
l_Lean_Elab_Term_expandCDot_x3f___closed__3 = _init_l_Lean_Elab_Term_expandCDot_x3f___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandCDot_x3f___closed__3);
l_Lean_Elab_Term_expandCDot_x3f___closed__4 = _init_l_Lean_Elab_Term_expandCDot_x3f___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandCDot_x3f___closed__4);
l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__1 = _init_l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__1);
l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__2 = _init_l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__2);
l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__3 = _init_l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__3);
l_Lean_Elab_Term_synthesizeInstMVarCore___closed__1 = _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_synthesizeInstMVarCore___closed__1);
l_Lean_Elab_Term_synthesizeInstMVarCore___closed__2 = _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_synthesizeInstMVarCore___closed__2);
l_Lean_Elab_Term_synthesizeInstMVarCore___closed__3 = _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_synthesizeInstMVarCore___closed__3);
l_Lean_Elab_Term_synthesizeInstMVarCore___closed__4 = _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_synthesizeInstMVarCore___closed__4);
l_Lean_Elab_Term_synthesizeInstMVarCore___closed__5 = _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_synthesizeInstMVarCore___closed__5);
l_Lean_Elab_Term_synthesizeInstMVarCore___closed__6 = _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_synthesizeInstMVarCore___closed__6);
l_Lean_Elab_Term_synthesizeInstMVarCore___closed__7 = _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_synthesizeInstMVarCore___closed__7);
l_Lean_Elab_Term_synthesizeInstMVarCore___closed__8 = _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_synthesizeInstMVarCore___closed__8);
l_Lean_Elab_Term_synthesizeInstMVarCore___closed__9 = _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_synthesizeInstMVarCore___closed__9);
l_Lean_Elab_Term_synthesizeInstMVarCore___closed__10 = _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_synthesizeInstMVarCore___closed__10);
l_Lean_Elab_Term_synthesizeInstMVarCore___closed__11 = _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_synthesizeInstMVarCore___closed__11);
l_Lean_Elab_Term_synthesizeInstMVarCore___closed__12 = _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_synthesizeInstMVarCore___closed__12);
l_Lean_Elab_Term_synthesizeInstMVarCore___closed__13 = _init_l_Lean_Elab_Term_synthesizeInstMVarCore___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_synthesizeInstMVarCore___closed__13);
l_Lean_Elab_Term_tryCoe___closed__1 = _init_l_Lean_Elab_Term_tryCoe___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_tryCoe___closed__1);
l_Lean_Elab_Term_tryCoe___closed__2 = _init_l_Lean_Elab_Term_tryCoe___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_tryCoe___closed__2);
l_Lean_Elab_Term_tryCoe___closed__3 = _init_l_Lean_Elab_Term_tryCoe___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_tryCoe___closed__3);
l_Lean_Elab_Term_tryCoe___closed__4 = _init_l_Lean_Elab_Term_tryCoe___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_tryCoe___closed__4);
l___private_Lean_Elab_Term_7__isMonad_x3f___closed__1 = _init_l___private_Lean_Elab_Term_7__isMonad_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Term_7__isMonad_x3f___closed__1);
l___private_Lean_Elab_Term_7__isMonad_x3f___closed__2 = _init_l___private_Lean_Elab_Term_7__isMonad_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Term_7__isMonad_x3f___closed__2);
l_Lean_Elab_Term_tryLiftAndCoe___closed__1 = _init_l_Lean_Elab_Term_tryLiftAndCoe___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_tryLiftAndCoe___closed__1);
l_Lean_Elab_Term_tryLiftAndCoe___closed__2 = _init_l_Lean_Elab_Term_tryLiftAndCoe___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_tryLiftAndCoe___closed__2);
l_Lean_Elab_Term_tryLiftAndCoe___closed__3 = _init_l_Lean_Elab_Term_tryLiftAndCoe___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_tryLiftAndCoe___closed__3);
l_Lean_Elab_Term_tryLiftAndCoe___closed__4 = _init_l_Lean_Elab_Term_tryLiftAndCoe___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_tryLiftAndCoe___closed__4);
l_Lean_Elab_Term_tryLiftAndCoe___closed__5 = _init_l_Lean_Elab_Term_tryLiftAndCoe___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_tryLiftAndCoe___closed__5);
l_Lean_Elab_Term_tryLiftAndCoe___closed__6 = _init_l_Lean_Elab_Term_tryLiftAndCoe___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_tryLiftAndCoe___closed__6);
l_Lean_Elab_Term_tryLiftAndCoe___closed__7 = _init_l_Lean_Elab_Term_tryLiftAndCoe___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_tryLiftAndCoe___closed__7);
l___private_Lean_Elab_Term_10__postponeElabTerm___closed__1 = _init_l___private_Lean_Elab_Term_10__postponeElabTerm___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Term_10__postponeElabTerm___closed__1);
l___private_Lean_Elab_Term_10__postponeElabTerm___closed__2 = _init_l___private_Lean_Elab_Term_10__postponeElabTerm___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Term_10__postponeElabTerm___closed__2);
l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__1 = _init_l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__1);
l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__2 = _init_l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__2);
l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__3 = _init_l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__3);
l_Lean_Elab_Term_elabUsingElabFns___closed__1 = _init_l_Lean_Elab_Term_elabUsingElabFns___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabUsingElabFns___closed__1);
l_Lean_Elab_Term_elabUsingElabFns___closed__2 = _init_l_Lean_Elab_Term_elabUsingElabFns___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabUsingElabFns___closed__2);
l_Lean_Elab_Term_elabUsingElabFns___closed__3 = _init_l_Lean_Elab_Term_elabUsingElabFns___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabUsingElabFns___closed__3);
l_Lean_Elab_Term_elabUsingElabFns___closed__4 = _init_l_Lean_Elab_Term_elabUsingElabFns___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabUsingElabFns___closed__4);
l_Lean_Elab_Term_elabUsingElabFns___closed__5 = _init_l_Lean_Elab_Term_elabUsingElabFns___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabUsingElabFns___closed__5);
l_Lean_Elab_Term_elabUsingElabFns___closed__6 = _init_l_Lean_Elab_Term_elabUsingElabFns___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabUsingElabFns___closed__6);
l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__1 = _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__1);
l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__2 = _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__2);
l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__3 = _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__3);
l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__4 = _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__4);
l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__5 = _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__5);
l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__6 = _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__6);
l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__7 = _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__7);
l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__8 = _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__8);
l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__9 = _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__9);
l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__10 = _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__10);
l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__11 = _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__11);
l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__12 = _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__12);
l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter = _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter);
l_Lean_Elab_Term_elabImplicitLambdaAux___closed__1 = _init_l_Lean_Elab_Term_elabImplicitLambdaAux___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabImplicitLambdaAux___closed__1);
l_Lean_Elab_Term_elabImplicitLambdaAux___closed__2 = _init_l_Lean_Elab_Term_elabImplicitLambdaAux___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabImplicitLambdaAux___closed__2);
l_Lean_Elab_Term_elabTermAux___main___closed__1 = _init_l_Lean_Elab_Term_elabTermAux___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabTermAux___main___closed__1);
l___private_Lean_Elab_Term_15__tryCoeSort___closed__1 = _init_l___private_Lean_Elab_Term_15__tryCoeSort___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Term_15__tryCoeSort___closed__1);
l___private_Lean_Elab_Term_15__tryCoeSort___closed__2 = _init_l___private_Lean_Elab_Term_15__tryCoeSort___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Term_15__tryCoeSort___closed__2);
l___private_Lean_Elab_Term_15__tryCoeSort___closed__3 = _init_l___private_Lean_Elab_Term_15__tryCoeSort___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Term_15__tryCoeSort___closed__3);
l___private_Lean_Elab_Term_15__tryCoeSort___closed__4 = _init_l___private_Lean_Elab_Term_15__tryCoeSort___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Term_15__tryCoeSort___closed__4);
l___private_Lean_Elab_Term_15__tryCoeSort___closed__5 = _init_l___private_Lean_Elab_Term_15__tryCoeSort___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Term_15__tryCoeSort___closed__5);
l___private_Lean_Elab_Term_15__tryCoeSort___closed__6 = _init_l___private_Lean_Elab_Term_15__tryCoeSort___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Term_15__tryCoeSort___closed__6);
l___private_Lean_Elab_Term_15__tryCoeSort___closed__7 = _init_l___private_Lean_Elab_Term_15__tryCoeSort___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Term_15__tryCoeSort___closed__7);
l_Lean_Elab_Term_mkAuxName___closed__1 = _init_l_Lean_Elab_Term_mkAuxName___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkAuxName___closed__1);
l_Lean_Elab_Term_mkAuxName___closed__2 = _init_l_Lean_Elab_Term_mkAuxName___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkAuxName___closed__2);
l_Lean_Elab_Term_mkAuxName___closed__3 = _init_l_Lean_Elab_Term_mkAuxName___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_mkAuxName___closed__3);
l___regBuiltin_Lean_Elab_Term_elabProp___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabProp___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProp___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabProp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabSort___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabSort___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSort___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabSort(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabTypeStx(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabHole___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabHole___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabHole___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabHole(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabNamedHole___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabNamedHole___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNamedHole___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabNamedHole(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_mkTacticMVar___closed__1 = _init_l_Lean_Elab_Term_mkTacticMVar___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkTacticMVar___closed__1);
l_Lean_Elab_Term_mkTacticMVar___closed__2 = _init_l_Lean_Elab_Term_mkTacticMVar___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkTacticMVar___closed__2);
l_Lean_Elab_Term_elabTacticBlock___closed__1 = _init_l_Lean_Elab_Term_elabTacticBlock___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabTacticBlock___closed__1);
l_Lean_Elab_Term_elabTacticBlock___closed__2 = _init_l_Lean_Elab_Term_elabTacticBlock___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabTacticBlock___closed__2);
l_Lean_Elab_Term_elabTacticBlock___closed__3 = _init_l_Lean_Elab_Term_elabTacticBlock___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabTacticBlock___closed__3);
l___regBuiltin_Lean_Elab_Term_elabTacticBlock___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabTacticBlock___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabTacticBlock___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabTacticBlock(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabByTactic___closed__1 = _init_l_Lean_Elab_Term_elabByTactic___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabByTactic___closed__1);
l_Lean_Elab_Term_elabByTactic___closed__2 = _init_l_Lean_Elab_Term_elabByTactic___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabByTactic___closed__2);
l_Lean_Elab_Term_elabByTactic___closed__3 = _init_l_Lean_Elab_Term_elabByTactic___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabByTactic___closed__3);
l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabByTactic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__1 = _init_l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__1);
l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__2 = _init_l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__2);
l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__3 = _init_l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__3);
l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__4 = _init_l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__4);
l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__5 = _init_l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Term_18__mkPairsAux___main___closed__5);
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
l___regBuiltin_Lean_Elab_Term_expandListLit___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandListLit___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandListLit___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandListLit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_expandArrayLit___closed__1 = _init_l_Lean_Elab_Term_expandArrayLit___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandArrayLit___closed__1);
l_Lean_Elab_Term_expandArrayLit___closed__2 = _init_l_Lean_Elab_Term_expandArrayLit___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandArrayLit___closed__2);
l_Lean_Elab_Term_expandArrayLit___closed__3 = _init_l_Lean_Elab_Term_expandArrayLit___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandArrayLit___closed__3);
l_Lean_Elab_Term_expandArrayLit___closed__4 = _init_l_Lean_Elab_Term_expandArrayLit___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandArrayLit___closed__4);
l_Lean_Elab_Term_expandArrayLit___closed__5 = _init_l_Lean_Elab_Term_expandArrayLit___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandArrayLit___closed__5);
l_Lean_Elab_Term_expandArrayLit___closed__6 = _init_l_Lean_Elab_Term_expandArrayLit___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_expandArrayLit___closed__6);
l_Lean_Elab_Term_expandArrayLit___closed__7 = _init_l_Lean_Elab_Term_expandArrayLit___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_expandArrayLit___closed__7);
l_Lean_Elab_Term_expandArrayLit___closed__8 = _init_l_Lean_Elab_Term_expandArrayLit___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_expandArrayLit___closed__8);
l_Lean_Elab_Term_expandArrayLit___closed__9 = _init_l_Lean_Elab_Term_expandArrayLit___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_expandArrayLit___closed__9);
l___regBuiltin_Lean_Elab_Term_expandArrayLit___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandArrayLit___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandArrayLit___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandArrayLit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_mkConst___closed__1 = _init_l_Lean_Elab_Term_mkConst___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkConst___closed__1);
l_Lean_Elab_Term_mkConst___closed__2 = _init_l_Lean_Elab_Term_mkConst___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkConst___closed__2);
l_Lean_Elab_Term_mkConst___closed__3 = _init_l_Lean_Elab_Term_mkConst___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_mkConst___closed__3);
l_Lean_Elab_Term_mkConst___closed__4 = _init_l_Lean_Elab_Term_mkConst___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_mkConst___closed__4);
l_Lean_Elab_Term_mkConst___closed__5 = _init_l_Lean_Elab_Term_mkConst___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_mkConst___closed__5);
l_Lean_Elab_Term_resolveName___closed__1 = _init_l_Lean_Elab_Term_resolveName___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__1);
l_Lean_Elab_Term_resolveName___closed__2 = _init_l_Lean_Elab_Term_resolveName___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__2);
l_Lean_Elab_Term_resolveName___closed__3 = _init_l_Lean_Elab_Term_resolveName___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__3);
l_Lean_Elab_Term_resolveName___closed__4 = _init_l_Lean_Elab_Term_resolveName___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__4);
l_Lean_Elab_Term_resolveName___closed__5 = _init_l_Lean_Elab_Term_resolveName___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__5);
l_Lean_Elab_Term_resolveName___closed__6 = _init_l_Lean_Elab_Term_resolveName___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__6);
l_Lean_Elab_Term_resolveName___closed__7 = _init_l_Lean_Elab_Term_resolveName___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__7);
l_Lean_Elab_Term_resolveName___closed__8 = _init_l_Lean_Elab_Term_resolveName___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__8);
l_Lean_Elab_Term_resolveName___closed__9 = _init_l_Lean_Elab_Term_resolveName___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__9);
l_Lean_Elab_Term_elabBadCDot___rarg___closed__1 = _init_l_Lean_Elab_Term_elabBadCDot___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabBadCDot___rarg___closed__1);
l_Lean_Elab_Term_elabBadCDot___rarg___closed__2 = _init_l_Lean_Elab_Term_elabBadCDot___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabBadCDot___rarg___closed__2);
l_Lean_Elab_Term_elabBadCDot___rarg___closed__3 = _init_l_Lean_Elab_Term_elabBadCDot___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabBadCDot___rarg___closed__3);
l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabBadCDot___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabBadCDot(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabRawStrLit___closed__1 = _init_l_Lean_Elab_Term_elabRawStrLit___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabRawStrLit___closed__1);
l_Lean_Elab_Term_elabRawStrLit___closed__2 = _init_l_Lean_Elab_Term_elabRawStrLit___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabRawStrLit___closed__2);
l_Lean_Elab_Term_elabRawStrLit___closed__3 = _init_l_Lean_Elab_Term_elabRawStrLit___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabRawStrLit___closed__3);
l___regBuiltin_Lean_Elab_Term_elabRawStrLit___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabRawStrLit___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabRawStrLit___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabRawStrLit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabStr___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabStr___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabStr___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabStr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabRawNumLit___closed__1 = _init_l_Lean_Elab_Term_elabRawNumLit___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabRawNumLit___closed__1);
l___regBuiltin_Lean_Elab_Term_elabRawNumLit___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabRawNumLit___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabRawNumLit___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabRawNumLit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabNum___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabNum___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNum___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabNum(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabRawCharLit___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabRawCharLit___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabRawCharLit___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabRawCharLit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabChar___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabChar___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabChar___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabChar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabQuotedName___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabQuotedName(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_MetaHasEval___rarg___closed__1 = _init_l_Lean_Elab_Term_MetaHasEval___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_MetaHasEval___rarg___closed__1);
l_Lean_Elab_Term_MetaHasEval___rarg___closed__2 = _init_l_Lean_Elab_Term_MetaHasEval___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_MetaHasEval___rarg___closed__2);
l_Lean_Elab_Term_MetaHasEval___rarg___closed__3 = _init_l_Lean_Elab_Term_MetaHasEval___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_MetaHasEval___rarg___closed__3);
l_Lean_Elab_Term_MetaHasEval___rarg___closed__4 = _init_l_Lean_Elab_Term_MetaHasEval___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_MetaHasEval___rarg___closed__4);
l_Lean_Elab_Term_MetaHasEval___rarg___closed__5 = _init_l_Lean_Elab_Term_MetaHasEval___rarg___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_MetaHasEval___rarg___closed__5);
l_Lean_Elab_Term_MetaHasEval___rarg___closed__6 = _init_l_Lean_Elab_Term_MetaHasEval___rarg___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_MetaHasEval___rarg___closed__6);
l___private_Lean_Elab_Term_24__regTraceClasses___closed__1 = _init_l___private_Lean_Elab_Term_24__regTraceClasses___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Term_24__regTraceClasses___closed__1);
res = l___private_Lean_Elab_Term_24__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
